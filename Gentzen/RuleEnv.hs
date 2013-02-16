{-# LANGUAGE DeriveFoldable, DeriveTraversable, DeriveFunctor #-}
module Gentzen.RuleEnv where

import Gentzen.Rule
import Gentzen.TypeLevel
import Data.Maybe
import Data.Foldable
import Data.Traversable

newtype Δ r a = Δ { lookup :: r -> Rule a } deriving (Functor)






extend :: Δ r a -> Rule a -> Δ (Suc r) a
extend (Δ f) r = Δ (maybe r f)

ruleMap :: (Rule a -> Rule b) -> Δ r a -> Δ r b
ruleMap f (Δ l) = Δ (f . l)

shaveVars :: (Δ r (Suc a)) -> (Δ r a)
shaveVars = fmap fromJust

shave :: Δ (Suc r) a -> Δ r a
shave (Δ f) = (Δ (f.suc))
