{-# LANGUAGE ExistentialQuantification, GADTs, TypeOperators, DataKinds, KindSignatures, ScopedTypeVariables, TypeFamilies, DeriveFunctor, FlexibleInstances, OverloadedStrings, ImplicitParams #-}
module Gentzen.Metalogic where

import Gentzen.Rule
import Gentzen.Unification
import Gentzen.Vector as V
import Gentzen.TypeLevel
import Gentzen.FreeSubst
import Gentzen.Equation
import Gentzen.Typechecker
import Gentzen.Term
import Gentzen.TypeEnv (Γ)
import qualified Gentzen.TypeEnv as TE
import Gentzen.RuleEnv (Δ)
import qualified Gentzen.RuleEnv as RE

data ProofTree a r = forall n. ProvenBy (Rule' n a) (r, FreeSubst (a :+: n))
                   | Unproven (Rule a)
                   | Inline   (Term Raw a) (r, FreeSubst a) [ProofTree a r]

instance Functor (ProofTree a) where
    fmap f (ProvenBy rl (r, subst)) = ProvenBy rl (f r, subst)
    fmap f (Unproven a) = Unproven a
    fmap f (Inline e (r, subst) cs) = Inline e (f r, subst) (map (fmap f) cs)


data ProofStatement a r = ForAll (Maybe String) Type (ProofStatement (Suc a) r)
                        | Lemma (Maybe String) (ProofStatement a r) (ProofStatement a (Suc r))
                        | Assuming (Maybe String) (Rule a) (ProofStatement a (Suc r))
                        | Show (ProofTree a r)
                        deriving (Functor)


instance Functor (Flip ProofTree r) where
   fmap f (Flip (ProvenBy ρ (r, σ)))  = Flip (ProvenBy (fmap f ρ) (r, fmap undefined σ))
   fmap f (Flip (Unproven ρ))         = Flip (Unproven (fmap f ρ))
   fmap f (Flip (Inline t (r, σ) cs)) = Flip (Inline (fmap f t) (r, fmap f σ) (map (fmap' f) cs))

instance Functor (Flip ProofStatement r) where
   fmap f (Flip (ForAll str τ st)) = Flip $ ForAll str τ $ fmap' (fmap f) st
   fmap f (Flip (Lemma str st st')) = Flip $ Lemma str (fmap' f st) $ fmap' f st'
   fmap f (Flip (Assuming str ρ st)) = Flip $ Assuming str (fmap f ρ) $ fmap' f st
   fmap f (Flip (Show t)) = Flip $ Show $ fmap' f t

rule :: ProofStatement a r -> Rule a
rule (ForAll s τ st) = abstractRule s τ $ rule $ st
rule (Assuming n r s) = addPremise r $ rule s
rule (Lemma n l s) = rule s
rule (Show pt) = ruleTree pt

ruleTree :: ProofTree a r -> Rule a
ruleTree (Unproven ρ)   = ρ
ruleTree (ProvenBy (Holds' a b c) _) = Holds a b c
ruleTree (Inline t r pt) = Holds Nil [] t


data Φ ::  * -> * -> Nat -> Nat -> * where
  EmptyC  :: Φ a r Zero Zero
  ForAllC :: Φ a r n m -> Maybe String -> Type -> Φ a r ('Suc n) m
  LemmaC₁ :: Φ a r n m -> Maybe String -> ProofStatement (a :+: n) (r :+: 'Suc m)
          -> Φ a r n m
  LemmaC₂ :: Φ a r n m -> Maybe String -> ProofStatement (a :+: n) (r :+: m)
          -> Φ a r n ('Suc m)
  AssumingC :: Φ a r n m -> Maybe String -> Rule (a :+: n)
            -> Φ a r n ('Suc m)
  TreeC   :: Φ a r n m -> Φ a r n m
  InlineC :: Φ a r n m -> Term Raw (a :+: n) -> (r :+: m, FreeSubst (a :+: n))
          -> [ProofTree (a :+: n) (r :+: m)] -> [ProofTree (a :+: n) (r :+: m)]
          -> Φ a r n m

data Context a r n m = Q { typeEnv   :: Γ (a :+: n)
                         , ruleEnv   :: Δ (r :+: m) (a :+: n)
                         , equations :: Ξ a
                         , stack     :: Φ a r n m
                         }

data Q a r = forall n m. (:>) (Context a r n m) (ProofStatement (a :+: n) (r :+: m))
           | forall n m. (:<) (Context a r n m) (ProofStatement (a :+: n) (r :+: m), Rule (a :+: n))

data ProofError = PrE String

contextVars :: Φ a r n m -> Vec n Type
contextVars (ForAllC φ x τ) = Cons x τ $ contextVars φ
contextVars (LemmaC₁ φ r π) = contextVars φ
contextVars (LemmaC₂ φ r π) = contextVars φ
contextVars (AssumingC φ x ρ) = contextVars φ
contextVars (TreeC φ) = contextVars φ
contextVars (InlineC φ e ρ ls rs) = contextVars φ

contextRules :: Φ a r n m -> Vec m (Rule (a :+: n))
contextRules (ForAllC φ x τ :: Φ a r n m)
   | Refl <- sequenceN (undefined :: a) (V.length $ contextVars φ)
   = fmap (fmap suc) $ contextRules φ
contextRules (LemmaC₁ φ x π) = contextRules φ
contextRules (LemmaC₂ φ x π) = Cons x (rule π) $ contextRules φ
contextRules (AssumingC φ x ρ) = Cons x ρ $ contextRules φ
contextRules (TreeC φ) = contextRules φ
contextRules (InlineC φ e ρ ls rs) = contextRules φ

wellformed :: Γ a -> Rule a -> Bool
wellformed γ (Holds τs ρs e)
   | γ' <- expandDomain τs γ
   , typecheck γ' e "Prop"
   , all (wellformed γ') ρs
   = True
   | otherwise = False

--FINISH TODO
(||-) :: (Eq a) => (SNat n, Γ (a :+: n), Ξ a) -> Equation (Rule (a :+: n)) -> Bool
(n , γ, ξ :: Ξ a) ||- (Holds τs ρp e :=: Holds τs' ρp' e')
        | Just Refl <- V.eq τs τs'
        , Refl <- plusNCollect (undefined :: a) n (V.length τs)
        , (addNat n (V.length τs), τs `expandDomain` γ, ξ) |- e :=: e'
        , all ((addNat n (V.length τs), τs `expandDomain` γ,ξ) ||-) (zipWith (:=:) ρp ρp')
        = True
        | otherwise = False

(|-) :: (Eq a) => (SNat n, Γ (a :+: n), Ξ a) -> Equation (Term Raw (a :+: n)) -> Bool
(|-) (n, γ, ξ) e
 | Right e' <- runTCM $ typecheckEq γ e
 = checkSolution [fmap (λ' undefined) e'] ξ

infixl 3 ||-
infixl 3 |-
next :: (Eq a) => Q a r -> Q a r
next (Q γ δ ξ φ :> ForAll x τ π :: Q a r)
   | Refl <- sequenceN (undefined :: a) (V.length $ contextVars φ)
   = Q (TE.extend γ τ) (fmap suc δ) ξ (ForAllC φ x τ) :> π
next (Q γ δ ξ (ForAllC φ x τ) :< (π , ρ) :: Q a r)
   | Refl <- sequenceN (undefined :: a) (V.length $ contextVars φ)
   = Q (TE.shave γ) (RE.shaveVars δ) ξ φ :< (ForAll x τ π, abstractRule x τ ρ)
next (Q γ δ ξ φ :> Assuming r ρ π :: Q a r)
   | Refl <- sequenceN (undefined :: r) (V.length $ contextRules φ)
   , wellformed γ ρ
   = Q γ (RE.extend δ ρ) ξ (AssumingC φ r ρ) :> π
next (Q γ δ ξ (AssumingC φ r ρ) :< (π , ρ') :: Q a r)
   | Refl <- sequenceN (undefined :: r) (V.length $ contextRules φ)
   = Q γ (RE.shave δ) ξ φ :< (Assuming r ρ π , addPremise ρ ρ')
next (Q γ δ ξ φ :> Lemma r π₁ π₂ :: Q a r)
   | Refl <- sequenceN (undefined :: r) (V.length $ contextRules φ)
   = Q γ δ ξ (LemmaC₁ φ r π₂) :> π₁
next (Q γ δ ξ (LemmaC₁ φ r π₂) :< (π₁ , ρ) :: Q a r)
   | Refl <- sequenceN (undefined :: r) (V.length $ contextRules φ)
   = Q γ (RE.extend δ ρ) ξ (LemmaC₂ φ r π₁) :> π₂
next (Q γ δ ξ (LemmaC₂ φ r π₁) :< (π₂ , ρ) :: Q a r)
   | Refl <- sequenceN (undefined :: r) (V.length $ contextRules φ)
   = Q γ (RE.shave δ) ξ φ :< (Lemma r π₁ π₂ , ρ)
next (Q γ δ ξ φ :> Show (Unproven ρ))
   | wellformed γ ρ
   = Q γ δ ξ φ :< (Show (Unproven ρ), ρ)
next (Q γ δ ξ φ :> Show (Inline e (r, σ) (t:ts)))
   | typecheck γ e "Prop"
   , n  <- V.length $ contextVars φ
   , ρ  <- RE.lookup δ r
   , ρ' <- instantiate ρ σ
   , (n, ξ) ||- ρ' :=: Holds Nil (map ruleTree (t:ts)) e
   = Q γ δ ξ (InlineC φ e (r,σ) [] ts) :> Show t
next (Q γ δ ξ φ :> Show (Inline e (r, σ) []))
   | typecheck γ e "Prop"
   , n  <- V.length $ contextVars φ
   , ρ  <- RE.lookup δ r
   , Holds Nil [] e' <- instantiate ρ σ
   , (n, ξ) |- e :=: e'
   = Q γ δ ξ φ :< (Show (Inline e (r, σ) []), Holds Nil [] e)
next (Q γ δ ξ (InlineC φ e (r, σ) ls []) :< (Show π, ρ))
   = Q γ δ ξ φ :< (Show $ Inline e (r, σ) (ls ++ [π]), Holds Nil [] e)
next (Q γ δ ξ (InlineC φ e (r, σ) ls (r':rs)) :< (Show π, ρ))
   = Q γ δ ξ (InlineC φ e (r, σ) (ls ++ [π]) rs) :> Show r'
next (Q γ δ ξ φ :> Show (ProvenBy ρ (r, σ)) :: Q a r)
   | Holds' τs ρp e <- ρ
   , n  <- V.length $ contextVars φ
   , n' <- V.length τs
   , ρ' <- RE.lookup δ r
   , Refl <- plusNCollect (undefined :: a) n n'
   , ρ'' <- instantiate (fmap (upN n') ρ') σ
   , (addNat n n', ξ) ||- ρ'' :=: Holds Nil ρp e
   = Q γ δ ξ φ :< (Show (ProvenBy ρ (r, σ)), hideIntros ρ)
