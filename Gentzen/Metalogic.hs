{-# LANGUAGE ExistentialQuantification, GADTs, TypeOperators, DataKinds, KindSignatures, ScopedTypeVariables, TypeFamilies, DeriveFunctor, FlexibleInstances #-}
module Gentzen.Metalogic where

import Gentzen.Rule
import Gentzen.Unification
import Gentzen.Vector as V
import Gentzen.TypeLevel
import Gentzen.Term

data ProofTree a r = ProvenBy (Rule a) (r, Solution a)
                   | Unproven (Rule a) String
                   | Inline   (Term Raw a) (r, Solution a) [ProofTree a r]
                   deriving (Functor)


data ProofStatement a r = ForAll (Maybe String) Type (ProofStatement (Suc a) r)
                        | Lemma (Maybe String) (ProofStatement a r) (ProofStatement a (Suc r))
                        | Assuming (Maybe String) (Rule a) (ProofStatement a (Suc r))
                        | Show (ProofTree a r)
                        deriving (Functor)


instance Functor (Flip ProofTree r) where
   fmap f (Flip (ProvenBy ρ (r, (σ,ν))))  = Flip (ProvenBy (fmap f ρ) (r, (fmap f σ, map (fmap (fmap f)) ν)))
   fmap f (Flip (Unproven ρ str))         = Flip (Unproven (fmap f ρ) str)
   fmap f (Flip (Inline t (r, (σ,ν)) cs)) = Flip (Inline (fmap f t) (r, (fmap f σ, map (fmap (fmap f)) ν)) (map (fmap' f) cs))

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
ruleTree (Unproven ρ n) = ρ
ruleTree (ProvenBy ρ _) = ρ
ruleTree (Inline t r pt) = Holds Nil [] t

data ViewType = PS | PT | TY | TR | RL

data ViewTypeS (t :: ViewType) where
  PSs :: ViewTypeS PS
  PTs :: ViewTypeS PT
  TYs :: ViewTypeS TY
  RLs :: ViewTypeS RL

data Context :: ViewType -> * -> * -> Nat -> Nat -> * where
  EmptyC  :: Context PS a r Zero Zero
  ForAllC :: Context PS a r n m -> Maybe String -> Type -> Context PS a r ('Suc n) m
  LemmaC  :: Context PS a r n m -> Maybe String -> ProofStatement (a :+: n) (r :+: m)
          -> Context PS a r n ('Suc m)
  AssumingC :: Context PS a r n m -> Maybe String -> Rule (a :+: n)
            -> Context PS a r n ('Suc m)
  EmptyT  :: Context PS a r n m -> Context PT a r n m
  InlineT :: Context PT a r n m -> Term Raw (a :+: n) -> (r :+: m, Solution (a :+: n))
          -> [ProofTree (a :+: n) (r :+: m)] -> [ProofTree (a :+: n) (r :+: m)]
          -> Context PT a r n m
  EmptyR :: Context PS a r n m -> Maybe String -> ProofStatement (a :+: n) (Suc (r :+: m))
         -> Context RL a r n m
  HoldsC :: Context RL a r n m -> Maybe String -> Type -> Context RL a r ('Suc n) m
  TermC  :: Context RL a r n m -> [Rule (a :+: n)] -> Context TR a r n m
  SubruleC :: Context RL a r n m -> Term Raw (a :+: n) -> [Rule (a :+: n)] -> [Rule (a :+: n)]
           -> Context RL a r n m
  EmptyTY :: Context PS a r n m -> Maybe String -> ProofStatement (Suc (a :+: n)) (r :+: m) -> Context TY a r n m
  NewTY   :: Context PS a r n m -> Maybe String -> ProofStatement (a :+: n) (r :+: m) -> Context TY a r n m
  LeftTY  :: Context TY a r n m -> Type -> Context TY a r n m
  RightTY :: Context TY a r n m -> Type -> Context TY a r n m

type family Head (t :: ViewType) a r
type instance Head PS a r = ProofStatement a r
type instance Head PT a r = ProofTree a r
type instance Head TY a r = Type
type instance Head RL a r = Rule a

data Zipper t a r = forall n m. Zip (Context t a r n m) (Head t (a :+: n) (r :+: m))

data ProofError = PrE String

contextTypes :: Context t a r n m -> Vec n Type
contextTypes (EmptyC) = Nil
--TODO
contextRules :: Context t a r n m -> Vec m (Rule a)
contextRules (EmptyC) = Nil

inRule :: Zipper RL a r -> Either ProofError (Zipper RL a r)
inRule (Zip ctx (Holds (Cons s τ τs) t cs) :: Zipper RL a r)
   | n <- V.length (contextTypes ctx), Refl <- sequenceN (undefined :: a) n
   = Right $ Zip (HoldsC ctx s τ) (Holds τs t cs)
inRule (Zip ctx hd) = Left $ PrE "No variable quantifiers to select into"

outRule :: Zipper RL a r -> Either ProofError (Zipper RL a r)
outRule (Zip (HoldsC ctx s τ) (Holds τs t cs) :: Zipper RL a r)
   | n <- V.length (contextTypes ctx), Refl <- sequenceN (undefined :: a) n
   = Right $ Zip ctx (Holds (Cons s τ τs) t cs)
outRule _ = Left $ PrE "No variable quantifiers in context"

premises :: Zipper RL a r -> Either ProofError (Zipper RL a r)
premises (Zip c (Holds Nil (l:rs) t))
   = Right $ Zip (SubruleC c t [] rs) l
premises _ = Left $ PrE "No premises found"

unpremises :: Zipper RL a r -> Either ProofError (Zipper RL a r)
unpremises (Zip (SubruleC c t ls rs) i)
   = Right $ Zip c (Holds Nil (ls ++ i:rs) t)
unpremises _ = Left $ PrE "Unpremises not possible"

nextPremise :: Zipper RL a r -> Either ProofError (Zipper RL a r)
nextPremise (Zip (SubruleC c t ls (r:rs)) l)
  = Right $ Zip (SubruleC c t (l:ls) rs) r
nextPremises _ = Left $ PrE "No more premises in that direction"

prevPremise :: Zipper RL a r -> Either ProofError (Zipper RL a r)
prevPremise (Zip (SubruleC c t (l:ls) rs) r)
  = Right $ Zip (SubruleC c t ls (r:rs)) l
prevPremise _ = Left $ PrE "No more premises in that direction"

editAssumption :: Zipper PS a r -> Either ProofError (Zipper RL a r)
editAssumption (Zip ctx (Assuming n ρ t)) = Right $ Zip (EmptyR ctx n t) ρ
editAssumption _ = Left $ PrE "No assumption to edit"

doneAssumption :: Zipper RL a r -> Either ProofError (Zipper PS a r)
doneAssumption (Zip (EmptyR ctx n t) ρ) = Right $ Zip ctx (Assuming n ρ t)
doneAssumption _ = Left $ PrE "Move to the top of the rule first."

editType :: Zipper PS a r -> Either ProofError (Zipper TY a r)
editType (Zip ctx (ForAll n τ t)) = Right $ Zip (EmptyTY ctx n t) τ
editType _ = Left $ PrE "No type to edit"

doneType :: Zipper TY a r -> Either ProofError (Zipper PS a r)
doneType (Zip (EmptyTY ctx n t) τ) = Right $ Zip ctx (ForAll n τ t)
doneType (Zip (NewTY ctx n t) τ) = Right $ Zip ctx (ForAll n τ (fmap' suc t))
doneType _ = Left $ PrE "Move to the top of the rule first."

enter :: Zipper PS a r -> Either ProofError (Zipper PS a r)
enter (Zip c (ForAll s τ st) :: Zipper PS a r)
    | n <- V.length (contextTypes c), Refl <- sequenceN (undefined :: a) n
    = Right $ Zip (ForAllC c s τ) st
enter (Zip c (Lemma s ρ st) :: Zipper PS a r)
    | m <- V.length (contextRules c), Refl <- sequenceN (undefined :: r) m
    = Right $ Zip (LemmaC c s ρ) st
enter (Zip c (Assuming s ρ st) :: Zipper PS a r)
    | m <- V.length (contextRules c), Refl <- sequenceN (undefined :: r) m
    = Right $ Zip (AssumingC c s ρ) st
enter x = Left $ PrE "Cannot enter a proof goal"

exit :: Zipper PS a r -> Either ProofError (Zipper PS a r)
exit (Zip (ForAllC c nm τ) t :: Zipper PS a r)
   | n <- V.length (contextTypes c), Refl <- sequenceN (undefined :: a) n
   = Right $ Zip c (ForAll nm τ t)
exit (Zip (LemmaC c nm ρ) t :: Zipper PS a r)
   | m <- V.length (contextRules c), Refl <- sequenceN (undefined :: r) m
   = Right $ Zip c (Lemma nm ρ t)
exit (Zip (AssumingC c n ρ) t :: Zipper PS a r)
   | m <- V.length (contextRules c), Refl <- sequenceN (undefined :: r) m
   = Right $ Zip c (Assuming n ρ t)
exit z = Left $ PrE "Already at top level"

up :: Zipper PT a r -> Either ProofError (Zipper PT a r)
up (Zip (InlineT c t sol ls rs) it) = Right $ Zip c (Inline t sol (ls ++ it:rs))
up x = Left $ PrE "No parent nodes to ascend to"

down :: Zipper PT a r -> Either ProofError (Zipper PT a r)
down (Zip c (Inline t sol (ρ:ρs))) = Right $ Zip (InlineT c t sol [] ρs) ρ
down x = Left $ PrE "No child nodes to descend to"

left :: Zipper PT a r -> Either ProofError (Zipper PT a r)
left (Zip (InlineT c t sol (l:ls) rs) r) = Right $ Zip (InlineT c t sol ls (r:rs)) l
left x = Left $ PrE "No subgoals to the left"

right :: Zipper PT a r -> Either ProofError (Zipper PT a r)
right (Zip (InlineT c t sol ls (r:rs)) l) = Right $ Zip (InlineT c t sol (l:ls) rs) r
right x = Left $ PrE "No subgoals to the right"

done :: Zipper PT a r -> Either ProofError (Zipper PS a r)
done (Zip (EmptyT ctx) t)
   | isOK (ruleTree t) = Right $ Zip ctx (Show t)
   | otherwise         = Left  $ PrE "Unresolved metavariables in rule"
done x = Left $ PrE "Go up first"
