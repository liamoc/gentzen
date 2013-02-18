{-# LANGUAGE ExistentialQuantification, TypeOperators, GADTs, DeriveFunctor #-}
module Gentzen.Rule where

import Gentzen.Vector as V
import Gentzen.Term
import Gentzen.TypeLevel
import Gentzen.FreeSubst

data Rule a = forall n. Holds (Vec n Type) [Rule (a :+: n)] (Term Raw (a :+: n))
data Rule' n a = Holds' (Vec n Type) [Rule (a :+: n)] (Term Raw (a :+: n)) 

intros :: Rule' n a -> Vec n Type
intros (Holds' τs _ _) = τs

hideIntros :: Rule' n a -> Rule a
hideIntros (Holds' a b c) = Holds a b c


instance Functor Rule where
  fmap f (Holds τs rs r) = Holds τs (map (fmap f') rs) (fmap f' r)
    where f' = mapPlusN (V.length τs) f

instance Functor (Rule' n) where
  fmap f (Holds' τs rs r) = Holds' τs (map (fmap f') rs) (fmap f' r)
    where f' = mapPlusN (V.length τs) f


abstractRule :: Maybe String -> Type -> Rule (Suc a) -> Rule a
abstractRule n τ (Holds τs as c) = Holds (Cons n τ τs) as c

addPremise :: Rule a -> Rule a -> Rule a
addPremise r (Holds τs ps c) = Holds τs (fmap (upN $ V.length τs) r : ps) c

substRule :: (a -> Term Raw b) -> Rule a -> Rule b
substRule σ (Holds τs ρs c) = let σ' = liftSubst (V.length τs) σ
                               in Holds τs (map (substRule σ') ρs) (c >>= σ')

freeSubstRule :: FreeSubst a -> Rule a -> Rule a
freeSubstRule σ (Holds τs ρs c) = let σ' = fmap (upN (V.length τs)) σ
                                   in Holds τs (map (freeSubstRule σ') ρs) $ σ' `freeSubst` c


enfreshinate :: Rule a -> Rule a
enfreshinate (Holds τs rs c) = Holds Nil (map (substRule fresh) rs) (c >>= fresh)
  where freshSubst :: [String] -> Vec n Type -> (a -> Term Raw b) -> (a :+: n) -> Term Raw b
        freshSubst _ Nil f = f
        freshSubst (c:cs) (Cons s τ τs) f = freshSubst cs τs (maybe (Λ Nil (RA c τ) []) f)
        strings = map (("?"++) . show) [1..]
        fresh = freshSubst strings τs return

instantiate :: Rule a -> FreeSubst a -> Rule a
instantiate ρ σ = freeSubstRule σ (enfreshinate ρ)

isOK :: Rule a -> Bool
isOK (Holds τs rs r) = not (containsFree r) && all isOK rs
