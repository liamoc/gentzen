{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures, StandaloneDeriving #-}

module Gentzen.Vector (Vec (..), concatenate, reverse, length, fromList, zip, eq, name, toList, expandDomain, expandDomainN) where
import Data.Foldable
import Data.Maybe
import Data.Traversable
import Gentzen.TypeLevel
import Prelude hiding (length, zip, reverse)
import Control.Applicative

data Vec :: Nat -> * -> * where
  Nil  :: Vec Zero a
  Cons :: Maybe String -> a -> Vec n a -> Vec ('Suc n) a
deriving instance Show a => Show (Vec n a)

instance Functor (Vec n) where
  fmap f Nil = Nil
  fmap f (Cons n x xs) = Cons n (f x) (fmap f xs)

instance Foldable (Vec n) where
  foldMap f = foldMap f . toList
   where toList :: Vec n a -> [a]
         toList (Cons n x xs) = x : toList xs
         toList Nil = []

instance Traversable (Vec n) where
  traverse f Nil = pure Nil
  traverse f (Cons n x xs) = Cons n <$> f x <*> traverse f xs

concatenate :: Vec n a -> Vec n' a -> Vec (n `NatPlus` n') a
concatenate (Nil) xs = xs
concatenate (Cons s v ys) xs
  | Refl <- sucDistrib (length ys) (length xs)
  = Cons s v (concatenate ys xs)


length :: Vec n a -> SNat n
length Nil = SZero
length (Cons _ _ xs) = SSuc (length xs)

fromList :: [a] -> Exists (Flip Vec a)
fromList [] = ExI $ Flip $ Nil
fromList (x:xs) | ExI (Flip xs') <- fromList xs = ExI $ Flip $ Cons Nothing x xs'

zip :: Vec n a -> Vec n b -> Vec n (a,b)
zip Nil            Nil            = Nil
zip (Cons n₁ x xs) (Cons n₂ y ys) = Cons n₁ (x,y) $ zip xs ys

eq :: (Eq a) => Vec n a -> Vec m a -> Maybe (n :==: m)
eq Nil Nil = Just Refl
eq (Cons _ x xs) (Cons _ y ys) | x == y = cong <$> eq xs ys
eq _ _ = Nothing

expandDomain :: Vec n a -> (r -> a) -> (r :+: n -> a)
expandDomain Nil r = r
expandDomain (Cons n ρ ρs) r = expandDomain ρs (maybe ρ r)

expandDomainN :: Vec n a -> (r -> String) -> (r :+: n -> String)
expandDomainN Nil r = r
expandDomainN (Cons n ρ ρs) r = expandDomainN ρs (maybe (fromMaybe "_" n) r)

data VecZipper :: Nat -> * -> * where
  VZ :: Vec n a -> Maybe String -> a -> Vec m a -> VecZipper (n `NatPlus` 'Suc m) a

zipLeft :: VecZipper n a -> VecZipper n a
zipLeft (VZ (Cons ln l ls) mn m r) = VZ ls ln l (Cons mn m r)

zipRight :: VecZipper n a -> VecZipper n a
zipRight (VZ ls mn m (Cons rn r rs)) = VZ (Cons mn m ls) rn r rs

dereference :: VecZipper n a -> a
dereference (VZ l mn m r) = m

set :: VecZipper n a -> a -> VecZipper n a
set (VZ l mn _ r) m' = VZ l mn m' r

name :: VecZipper n a -> Maybe String
name (VZ l mn m r) = mn

reverse :: Vec n a -> Vec n a
reverse (Cons n ρ ρs) 
   | Refl <- sucDistrib (length ρs) (SZero)
   , Refl <- plusZero (length ρs)
   = concatenate (reverse ρs) (Cons n ρ Nil)
reverse (Nil) = Nil

setName :: VecZipper n a -> Maybe String -> VecZipper n a
setName (VZ l _ m r) mn = VZ l mn m r


