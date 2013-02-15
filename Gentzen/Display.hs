{-# LANGUAGE GADTs, ImplicitParams, DataKinds, TypeOperators, ScopedTypeVariables, TypeFamilies #-}
module Gentzen.Display where
import Gentzen.TypeLevel
import Gentzen.Term
import Gentzen.Vector as V
import Gentzen.Rule
import Gentzen.Metalogic
import Gentzen.Unification
import Gentzen.FreeSubst as F
import Gentzen.Equation
import Data.Maybe
import Control.Arrow

data family Pretty (t :: ViewType)

data instance Pretty TR = Lam [(String, Type)] String [Pretty TR]
                        | SelectedT (Pretty TR)

data instance Pretty RL = Rule [(String, Type)] [Pretty RL] (Pretty TR)
                        | SelectedR (Pretty RL)

data instance Pretty PS = Forall [(String, Type)] (Pretty PS)
                        | Assume [(String, Pretty RL)] (Pretty PS)
                        | LemmaI [(String, Pretty PS)] (Pretty PS)
                        | Shows  (Pretty PT)
                        | SelectedS (Pretty PS)
                        | Empty

newtype instance Pretty TY = PTY Type

data PrettySol = Sol [(String, Pretty TR)] [Equation (Pretty TR)]

data instance Pretty PT = Branch String PrettySol (Pretty TR) [Pretty PT]
                        | Goal String PrettySol (Pretty RL)
                        | Hole (Pretty RL)
                        | Selected (Pretty TR)

displayTerm :: (a -> String) -> Term Raw a -> Pretty TR
displayTerm e (Λ τs c cs) = Lam (mapToList τs) (toString c) (map (displayTerm e') cs)
  where e' = expandDomainN τs e
        toString (RA n τ) = '?':n
        toString (RV n)   = e' n

displayTerm' :: (a -> String) -> Term Typechecked a -> Pretty TR
displayTerm' e (Λ τs c cs) = Lam (mapToList τs) (toString c) (map (displayTerm' e') cs)
  where e' = expandDomainN τs e
        toString (A n τ) = '?':n
        toString (V n τ)   = e' n

mapToList :: Vec n Type -> [(String, Type)]
mapToList (Cons n τ τs) = (fromMaybe "_" n,τ):mapToList τs
mapToList Nil           = []

displayRule :: (a -> String) -> Rule a -> Pretty RL
displayRule e (Holds τs cs c) = Rule (mapToList τs) (map (displayRule e') cs) (displayTerm e' c)
   where e' = expandDomainN τs e

{-
  HoldsC :: Context RL a r n Zero -> Maybe String -> Type -> Context RL a r ('Suc n) Zero
  TermC  :: Context RL a r n Zero -> [Rule (a :+: n)] -> Context RL a r n Zero
  SubruleC :: Context RL a r n Zero -> Term Raw (a :+: n) -> [Rule (a :+: n)] -> [Rule (a :+: n)]
           -> Context RL a r n Zero
-}

displaySolution :: (a -> String) -> Solution a -> PrettySol
displaySolution e (subst, uniprob) = Sol (map (fst *** displayTerm e) $ F.toList subst)
                                         (map (fmap $ displayTerm' e) uniprob)

displayTree :: (a -> String) -> (r -> String) -> ProofTree a r -> Pretty PT
displayTree te re (ProvenBy rule (r, sol)) = Goal (re r) (displaySolution te sol) (displayRule te rule)
displayTree te re (Unproven rule str)      = Hole (displayRule te rule)
displayTree te re (Inline term (r,sol) cs) = Branch (re r) (displaySolution te sol)
                                                    (displayTerm te term) (map (displayTree te re) cs)

forallP s τ (Forall ls stmt) = Forall ((fromMaybe "_" s, τ):ls) stmt
forallP s τ t                = Forall [(fromMaybe "_" s, τ)   ] t

lemmaP s ρ (LemmaI ls stmt) = LemmaI ((fromMaybe "_" s, ρ):ls) stmt
lemmaP s ρ t                = LemmaI [(fromMaybe "_" s, ρ)]    t
assumingP s ρ (Assume ls stmt) = Assume ((fromMaybe "_" s, ρ):ls) stmt
assumingP s ρ t                = Assume [(fromMaybe "_" s, ρ)]    t

displayStmt :: (a -> String) -> (r -> String) -> ProofStatement a r -> Pretty PS
displayStmt te re (ForAll s τ st) = forallP s τ $ displayStmt te' re st
   where te' = expandDomainN (Cons s τ Nil) te
displayStmt te re (Assuming s ρ st) = assumingP s (displayRule te ρ) $ displayStmt te re' st
   where re' = expandDomainN (Cons s ρ Nil) re
displayStmt te re (Lemma s ρ st) = lemmaP s (displayStmt te re ρ) $ displayStmt te re' st
   where re' = expandDomainN (Cons s ρ Nil) re
displayStmt te re (Show t) = Shows $ displayTree te re t

displayContext :: (a -> String) -> (r -> String)
               -> Context t a r n m
               -> Pretty t -> Pretty PS
displayContext te re EmptyC s = s
displayContext te re (ForAllC ctx str τ) st
    = displayContext te re ctx $ forallP str τ st
displayContext te re (AssumingC ctx str ρ) st
    | te' <- expandDomainN (contextTypes ctx) te
    = displayContext te re ctx $ assumingP str (displayRule te' ρ) st
displayContext te re (LemmaC ctx str ρ) st
    | te' <- expandDomainN (contextTypes ctx) te
    , re' <- expandDomainN (contextRules ctx) re
    = displayContext te re ctx $ lemmaP str (displayStmt te' re' ρ) st
displayContext te re (EmptyT c) t = displayContext te re c (Shows t)
displayContext te re (InlineT ctx t (r,sol) ls rs) c
    | te' <- expandDomainN (contextTypes ctx) te
    , re' <- expandDomainN (contextRules ctx) re
    = displayContext te re ctx $ Branch (re' r) (displaySolution te' sol)
                                                (displayTerm te' t)
                                                (map (displayTree te' re') ls
                                                 ++ (c:map (displayTree te' re') rs))
displayContext te re (EmptyR ctx n st :: Context t a r n m) r
    | rules <- contextRules ctx
    , te' <- expandDomainN (contextTypes ctx) te
    , re' <- maybe (fromMaybe "_" n) (expandDomainN rules re)
    , m <- V.length rules, Refl <- sequenceN (undefined :: r) m
    = displayContext te re ctx $ assumingP n r (displayStmt te' re' st)
displayContext te re (HoldsC ctx s τ :: Context t a r n m) (Rule τs cs c)
    = displayContext te re ctx $ Rule ((fromMaybe "_" s, τ):τs) cs c
displayContext te re (SubruleC ctx t ls rs) r
   | te' <- expandDomainN (contextTypes ctx) te
   = displayContext te re ctx $ Rule [] (map (displayRule te') ls ++ r:map (displayRule te') rs)
                                        (displayTerm te' t)
displayContext te re (EmptyTY ctx n st :: Context t a r n m) (PTY τ)
  | types <- contextTypes ctx
  , te' <- maybe (fromMaybe "_" n) (expandDomainN types te)
  , re' <- expandDomainN (contextRules ctx) re
  , n' <- V.length types, Refl <- sequenceN (undefined :: a) n'
  = displayContext te re ctx $ forallP n τ (displayStmt te' re' st)
displayContext te re (LeftTY  ctx β) (PTY α) = displayContext te re ctx $ PTY $ Fun α β
displayContext te re (RightTY ctx α) (PTY β) = displayContext te re ctx $ PTY $ Fun α β

{-
-}

