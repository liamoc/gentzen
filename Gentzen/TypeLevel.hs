{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, DataKinds, PolyKinds, UndecidableInstances, ScopedTypeVariables #-}
module Gentzen.TypeLevel where
import Control.Monad

data Nat = Zero | Suc Nat

data SNat :: Nat -> * where
  SZero :: SNat Zero
  SSuc  :: SNat n -> SNat ('Suc n)

data (:==:) :: a -> a -> * where
  Refl :: a :==: a

data Exists :: (a -> *) -> * where
  ExI :: f a -> Exists f

newtype Flip f a b = Flip { unflip :: f b a }

fmap' f x = unflip $ fmap f $ Flip x

cong :: (a :==: b) -> (f a :==: f b)
cong Refl = Refl

type Suc a = Maybe a

suc :: a -> Suc a
suc = Just
zero :: Suc a
zero = Nothing

type family (:+:) (a :: *) (b :: Nat) :: *
type instance (:+:) a Zero = a
type instance (:+:) a ('Suc b) = Suc a :+: b

upN ::  SNat n -> a -> a :+: n
upN SZero x = x
upN (SSuc s) x = upN s (suc x)

type family NatPlus (x :: Nat) (y :: Nat) :: Nat
type instance NatPlus Zero x = x
type instance NatPlus ('Suc y) x = NatPlus y ('Suc x)

sucDistrib :: SNat n -> SNat m -> (n `NatPlus` 'Suc m) :==: 'Suc (n `NatPlus` m)
sucDistrib SZero x = Refl
sucDistrib (SSuc n) x = sucDistrib n (SSuc x)

plusZero :: SNat n -> (n `NatPlus` Zero) :==: n
plusZero SZero = Refl
plusZero (SSuc n)
   | Refl <- sucDistrib n SZero
   = cong (plusZero n)

extract :: SNat n -> a :+: n -> Maybe a
extract SZero x = Just x
extract (SSuc n) x = join (extract n x)

mapPlusN :: SNat n -> (a -> b) -> (a :+: n) -> (b :+: n)
mapPlusN SZero f = f
mapPlusN (SSuc n) f = mapPlusN n (maybe Nothing (Just . f))

addComm :: SNat a -> SNat b -> (a `NatPlus` b) :==: (b `NatPlus` a)
addComm n SZero = plusZero n
addComm n (SSuc n') | Refl <- sucDistrib n n'
                    , Refl <- sucDistrib n' n
                    , Refl <- addComm n n'
                    = Refl

plusNCollect :: x -> SNat a -> SNat b ->  (x :+: (a `NatPlus` b))  :==: ((x :+: a) :+: b)
plusNCollect _ SZero x = Refl
plusNCollect (_ :: x) (SSuc n) m
   | Refl <- sucDistrib n m
   = plusNCollect (undefined :: Suc x) n m

addNat :: SNat a -> SNat b -> SNat (a `NatPlus` b)
addNat (SZero ) x = x
addNat (SSuc n) x = addNat n (SSuc x)

class Reify (n :: Nat) where
  reify :: SNat n

instance Reify Zero where
  reify = SZero

instance Reify n => Reify ('Suc n) where
  reify = SSuc reify

sequenceN :: a -> SNat n -> (Suc a :+: n) :==: Suc (a :+: n)
sequenceN _ SZero = Refl
sequenceN (_ :: a) (SSuc n) | Refl <- sequenceN (undefined :: Suc a) n = Refl

