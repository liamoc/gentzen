{-# LANGUAGE GADTs, ImplicitParams, DataKinds, TypeOperators, ScopedTypeVariables, TypeFamilies #-}
module Gentzen.Display where
import Gentzen.TypeLevel
import Gentzen.Term
import qualified Gentzen.Vector as V
import Gentzen.Vector (Vec (..))
import Gentzen.Rule
import Gentzen.Metalogic
import Gentzen.Unification
import Gentzen.FreeSubst as F
import Gentzen.Equation
import qualified Gentzen.TypeEnv as TE
import Data.Maybe
import Control.Arrow
import Data.List (intersperse)

data PrettyTerm = Lam [(String, Type)] String [PrettyTerm]
                | SelectedT PrettyTerm

data PrettyRule = Rule [(String, Type)] [PrettyRule] PrettyTerm
                | SelectedR PrettyRule

data PrettyStmt = Forall [(String, Type)] PrettyStmt
                | Assume [(String, PrettyRule)] PrettyStmt
                | LemmaI [(String, PrettyStmt)] PrettyStmt
                | Shows  PrettyTree
                | SelectedS PrettyStmt
                | Empty


type PrettySol = [(String, PrettyTerm)]

data PrettyTree = Branch String PrettySol PrettyTerm [PrettyTree]
                | Goal String PrettySol PrettyRule
                | Hole PrettyRule
                | Selected PrettyTerm

displayTerm :: (a -> String) -> Term Raw a -> PrettyTerm
displayTerm e (Λ τs c cs) = Lam (mapToList τs) (toString c) (map (displayTerm e') cs)
  where e' = V.expandDomainN τs e
        toString (RA n τ) = '?':n
        toString (RV n)   = e' n

displayTerm' :: (a -> String) -> Term Typechecked a -> PrettyTerm
displayTerm' e (Λ τs c cs) = Lam (mapToList τs) (toString c) (map (displayTerm' e') cs)
  where e' = V.expandDomainN τs e
        toString (A n τ) = '?':n
        toString (V n τ)   = e' n

mapToList :: Vec n Type -> [(String, Type)]
mapToList (Cons n τ τs) = (fromMaybe "_" n,τ):mapToList τs
mapToList Nil           = []

displayRule :: (a -> String) -> Rule a -> PrettyRule
displayRule e (Holds τs cs c) = Rule (mapToList τs) (map (displayRule e') cs) (displayTerm e' c)
   where e' = V.expandDomainN τs e

displaySolution :: (a -> String) -> FreeSubst a -> PrettySol
displaySolution e subst = map (fst *** displayTerm e) $ F.toList subst

displayTree :: (a -> String) -> (r -> String) -> ProofTree a r -> PrettyTree
displayTree te re (ProvenBy rule@(Holds' τs _ _) (r, sol))
     = Goal (re r) (displaySolution (τs `V.expandDomainN` te) sol) (displayRule te $ hideIntros rule)
displayTree te re (Unproven rule)          = Hole (displayRule te rule)
displayTree te re (Inline term (r,sol) cs) = Branch (re r) (displaySolution te sol)
                                                    (displayTerm te term) (map (displayTree te re) cs)

forallP s τ (Forall ls stmt) = Forall ((fromMaybe "_" s, τ):ls) stmt
forallP s τ t                = Forall [(fromMaybe "_" s, τ)   ] t

lemmaP s ρ (LemmaI ls stmt) = LemmaI ((fromMaybe "_" s, ρ):ls) stmt
lemmaP s ρ t                = LemmaI [(fromMaybe "_" s, ρ)]    t
assumingP s ρ (Assume ls stmt) = Assume ((fromMaybe "_" s, ρ):ls) stmt
assumingP s ρ t                = Assume [(fromMaybe "_" s, ρ)]    t

displayStmt :: (a -> String) -> (r -> String) -> ProofStatement a r -> PrettyStmt
displayStmt te re (ForAll s τ st) = forallP s τ $ displayStmt te' re st
   where te' = V.expandDomainN (Cons s τ Nil) te
displayStmt te re (Assuming s ρ st) = assumingP s (displayRule te ρ) $ displayStmt te re' st
   where re' = V.expandDomainN (Cons s ρ Nil) re
displayStmt te re (Lemma s ρ st) = lemmaP s (displayStmt te re ρ) $ displayStmt te re' st
   where re' = V.expandDomainN (Cons s ρ Nil) re
displayStmt te re (Show t) = Shows $ displayTree te re t

data PrettyContext = PForAll String Type
                   | PAssuming String PrettyRule
                   | PLemma₁ String PrettyStmt
                   | PLemma₂ String PrettyStmt
                   | PStep PrettyTerm (String, PrettySol) [PrettyTree] [PrettyTree]

displayContext :: Φ a r n m -> (a :+: n -> String) -> (r :+: m -> String) -> [PrettyContext]
displayContext (EmptyC) te re = []
displayContext (ForAllC φ x τ :: Φ a r n m) te re
   | Refl <- sequenceN (undefined :: a) (V.length (contextVars φ))
   = PForAll (fromMaybe "_" x) τ : displayContext φ (TE.shave te) re
displayContext (AssumingC φ x ρ :: Φ a r n m) te re
   | Refl <- sequenceN (undefined :: r) (V.length (contextRules φ))
   = PAssuming (fromMaybe "_" x) (displayRule te ρ) : displayContext φ te (TE.shave re)
displayContext (LemmaC₁ φ s π :: Φ a r n m) te re
   | n <- fromMaybe "_" s
   , Refl <- sequenceN (undefined :: r) (V.length (contextRules φ))
   = PLemma₁ n (displayStmt te (maybe n re) π) : displayContext φ te re
displayContext (LemmaC₂ φ s π :: Φ a r n m) te re
   | n <- fromMaybe "_" s
   , Refl <- sequenceN (undefined :: r) (V.length (contextRules φ))
   = PLemma₂ n (displayStmt te (TE.shave re) π) : displayContext φ te (TE.shave re)
displayContext (InlineC φ e (r, σ) ls rs) te re
   = PStep (displayTerm te e)
           (re r, displaySolution te σ)
           (map (displayTree te re) ls)
           (map (displayTree te re) rs)
   : displayContext φ te re
displayContext (TreeC x) te re = displayContext x te re

class Pretty a where
  ppr :: a -> String

instance Pretty PrettyContext where
  ppr (PForAll x τ) = "for all " ++ x ++ " : " ++ ppr τ ++ ", □"
  ppr (PAssuming x ρ) = "assuming " ++ x ++ " = \"" ++ ppr ρ ++ "\""
  ppr (PLemma₁ n π)   = "lemma " ++ n ++ " = □, " ++ ppr π
  ppr (PLemma₂ n π)   = "lemma " ++ n ++ " = " ++ ppr π ++ ", □"
  ppr (PStep e (r, σ) ls rs)
   = "step \"" ++ ppr e ++ "\" by " ++ r ++ " with [" ++ ppr σ ++ "] giving " ++ ppr' ls ++ " □ " ++ ppr' rs
   where ppr' ls = concat $ intersperse " " (map (++")") (map ("(" ++) (map ppr ls)))


instance Pretty PrettyTerm where
  ppr e = ppr' e False
   where ppr' (Lam [] x []) _ = x
         ppr' (Lam τs x ts) True  = "(" ++ ppr' (Lam τs x ts) False ++ ")"
         ppr' (Lam [] x ts) False = x ++ " " ++ concat (intersperse " " (map (flip ppr' True) ts))
         ppr' (Lam τs x ts) False = "λ(" ++ ppr τs ++ "). " ++  ppr' (Lam [] x ts) False


instance Pretty PrettyRule where
  ppr (Rule [] [] e) = ppr e
  ppr (Rule [] cs e) = "⟦" ++ concat (intersperse "; " (map ppr cs)) ++ "⟧⇒ " ++ ppr e
  ppr (Rule τs cs e) = "Λ(" ++ ppr τs ++ "). " ++ ppr (Rule [] cs e)

indent' n = unlines . map (replicate n ' '++) . lines
indent = indent' 2

instance Pretty PrettyStmt where
  ppr (Forall [] π) = ppr π
  ppr (Forall τs π) = "for all (" ++ ppr τs ++ "). \n" ++ indent (ppr π)
  ppr (Assume [] π) = ppr π
  ppr (Assume ((n,ρ):ρs) π) = "assume " ++ n ++ " = \"" ++ ppr ρ ++ "\",\n" ++ indent (ppr π)
  ppr (LemmaI [] π) = ppr π
  ppr (LemmaI ((n,π):πs) π₁) = let header =  "lemma " ++ n ++ " = "
                                in header ++ drop (length header) (indent' (length header) $ ppr π)
                                ++ ";\n" ++ indent (ppr $ LemmaI πs π₁)
  ppr (Shows t) = ppr t

instance Pretty Type where
  ppr τ = ppr' τ False
   where ppr' (TA s) _ = s
         ppr' (Fun τ₁ τ₂) True  = "(" ++ ppr' τ₁ True ++ " → " ++ ppr' τ₂ False ++ ")"
         ppr' (Fun τ₁ τ₂) False =        ppr' τ₁ True ++ " → " ++ ppr' τ₂ False

instance Pretty [(String, PrettyTerm)] where
  ppr [] = ""
  ppr ((n,t):[]) = n ++ " ∶= \"" ++ ppr t ++ "\""
  ppr ((n,t):y) = n ++ " ∶= \"" ++ ppr t ++ "\", " ++ ppr y

instance Pretty [(String, Type)] where
  ppr [] = ""
  ppr ((n,τ):[]) = n ++ " : " ++ ppr τ
  ppr ((n,τ):y) = n ++ " : " ++ ppr τ ++ ", " ++ ppr y

instance Pretty PrettyTree where
  ppr (Hole ρ) = "sorry \"" ++ ppr ρ ++ "\""
  ppr (Branch r σ e cs) = "step \"" ++ ppr e ++ "\" by " ++ r ++ " with [" ++ ppr σ ++ "] giving:\n"
                             ++ indent (concat $ intersperse "; \n" $ map ppr cs)
  ppr (Goal n σ ρ) = "show \"" ++ ppr ρ ++ "\" by " ++ n ++ " with [" ++ ppr σ ++ "]"

instance Pretty [PrettyContext] where
  ppr [] = "ε"
  ppr (x:xs) = ppr xs ++ "\n ∙ " ++ ppr x


displayState :: (a -> String ) -> (r -> String) -> Q a r -> String
displayState te re (Q _ _ _ φ :> π)       = ppr (displayContext φ te' re')
                                ++ "\n ▻ \n" ++ ppr (displayStmt te' re' π)
  where te' = contextVars φ `V.expandDomainN` te
        re' = contextRules φ `V.expandDomainN` re
displayState te re (Q _ _ _ φ :< (π , ρ)) = ppr (displayContext φ te' re')
                                ++ "\n ◅ \n " ++ ppr (displayStmt te' re' π)
  where te' = contextVars φ `V.expandDomainN` te
        re' = contextRules φ `V.expandDomainN` re
