{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, DeriveFunctor #-}
module Gentzen.FreeSubst (FreeSubst, lookup, freeSubst, singleton, fromList, null, toList) where

import Gentzen.Term
import Gentzen.TypeLevel
import Gentzen.Vector (Vec(..))

import qualified Data.Map as M
import Data.Map (Map)
import Data.List (foldl')
import Data.Monoid

import Prelude hiding (lookup, null)

newtype FreeSubst a = FS (Map (FreeName, Type) (Term Raw a)) deriving Functor

instance Show a => Show (FreeSubst a) where
  show (FS a) = show a

lookup :: FreeSubst a -> (FreeName, Type) -> Maybe (Term Raw a)
lookup (FS m) = flip M.lookup m

freeSubst :: FreeSubst a -> Term Raw a -> Term Raw a
freeSubst σ (Λ Nil (RV c  ) ts) = Λ Nil (RV c) $ map (freeSubst σ) ts
freeSubst σ (Λ Nil (RA ν τ) ts) | Just r <- lookup σ (ν,τ) = foldl' (.$) r  $ map (freeSubst σ) ts
                                | otherwise                = Λ Nil (RA ν τ) $ map (freeSubst σ) ts
freeSubst σ (Λ (Cons n τ τs) h ts) = λ (n, τ) (freeSubst (fmap suc σ) $ Λ τs h ts)

instance Monoid (FreeSubst a) where
   mempty = FS M.empty
   mappend (FS a) (FS b) = FS (M.map (freeSubst (FS b)) a `M.union` b)

singleton :: (String, Type) -> Term Raw a -> FreeSubst a
singleton k v = FS $ M.singleton k v

fromList :: [((String, Type),Term Raw a)] -> FreeSubst a
fromList  = mconcat . map (uncurry singleton)

null :: FreeSubst a -> Bool
null (FS a) = M.null a

toList :: FreeSubst a -> [((String,Type),Term Raw a)]
toList (FS a) = M.toList a
