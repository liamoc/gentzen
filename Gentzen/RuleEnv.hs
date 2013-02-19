{-# LANGUAGE DeriveFoldable, DeriveTraversable, DeriveFunctor #-}
module Gentzen.RuleEnv where

import Gentzen.Rule
import Gentzen.TypeLevel
import Data.Maybe
import Data.Foldable
import Data.Traversable
import Prelude as P

data Δ r a = Δ { lookup :: r -> Rule a
               , strs :: [(String, r)]
               } deriving (Functor)






extend :: Δ r a -> Maybe String -> Rule a -> Δ (Suc r) a
extend (Δ f m) (Just n) r = Δ (maybe r f) ((n, zero):map (fmap suc) m)

ruleMap :: (Rule a -> Rule b) -> Δ r a -> Δ r b
ruleMap f (Δ l m) = Δ (f . l) m

shaveVars :: (Δ r (Suc a)) -> (Δ r a)
shaveVars = fmap fromJust

lookupString :: (Δ r a) -> String -> Maybe r
lookupString (Δ _ x) = flip P.lookup x

shave :: Δ (Suc r) a -> Δ r a
shave (Δ f (x:xs)) = (Δ (f.suc) (map (fmap fromJust) xs))
