{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, DeriveFunctor, ScopedTypeVariables, FlexibleInstances #-}
module Gentzen.Term where
import Data.String
import Gentzen.TypeLevel
import Gentzen.Vector as V
import Control.Arrow
import Data.Foldable hiding (concat, and, any)
import Data.List (intersperse)
type FreeName = String

data Type = TA String
	       | Fun Type Type
          deriving (Eq,Show, Ord)
instance IsString Type where
  fromString = TA

data Raw a = RA FreeName Type
           | RV a
           deriving (Show, Functor, Eq)
data Typechecked a = A FreeName Type
                   | V a        Type
                   deriving (Show, Functor, Eq)

data Term r a where
  Λ :: Vec n Type -> r (a :+: n) -> [Term r (a :+: n)] -> Term r a




termeq :: (a -> a -> Bool) -> (Term Typechecked a -> Term Typechecked a -> Bool)
termeq ((===) :: a -> a -> Bool) (Λ (τs₁ :: Vec n Type) t₁ cs₁) (Λ τs₂ t₂ cs₂)
    | Just Refl <- V.eq τs₁ τs₂
    , tceq (lifteq (V.length τs₁) (===)) t₁ t₂
    , and $ zipWith (termeq (lifteq (V.length τs₁) (===))) cs₁ cs₂ = True
    | otherwise                                                    = False
 where tceq :: (b -> b -> Bool) -> Typechecked b -> Typechecked b -> Bool
       tceq f (A n t) (A n' t') = n == n' && t == t'
       tceq f (V n t) (V n' t') = f n n' && t == t'
       up1 :: (c -> c -> Bool) -> Suc c -> Suc c -> Bool
       up1 f (Just x) (Just y) = f x y
       up1 f (Nothing) (Nothing) = True
       up1 f _ _ = False

       lifteq :: SNat m -> (b -> b -> Bool) -> (b :+: m -> b :+: m -> Bool)
       lifteq SZero f = f
       lifteq (SSuc n) f = lifteq n (up1 f)



instance Eq b => Eq (Term Typechecked b) where
  (==) = termeq (==)
instance Show b => Show (Term Typechecked b) where
  show = showTerm show
    where showTerm :: (a -> String) -> Term Typechecked a -> String
          showTerm (s :: a -> String) (Λ (vec :: Vec n Type) x t)
             = "(Λ " ++ show vec ++ " " ++ showTC' (liftShow (V.length vec) s) x ++ " "
            ++ "[" ++ concat (intersperse "," (map (showTerm (liftShow (V.length vec) s)) t)) ++ "])"
            where
              showTC' :: (a :+: n -> String) -> Typechecked (a :+: n) -> String
              showTC' f (V a t) = "(V " ++ f a ++ show t ++  ")"
              showTC' _ (A f t) = "(A " ++ show f ++ " " ++ show t ++ ")"
instance Show b => Show (Term Raw b) where
  show = showTerm show
    where showTerm :: (a -> String) -> Term Raw a -> String
          showTerm (s :: a -> String) (Λ (vec :: Vec n Type) x t)
             = "(Λ " ++ show vec ++ " " ++ showRaw' (liftShow (V.length vec) s) x ++ " "
            ++ "[" ++ concat (intersperse "," (map (showTerm (liftShow (V.length vec) s)) t)) ++ "])"
            where
              showRaw' :: (a :+: n -> String) -> Raw (a :+: n) -> String
              showRaw' f (RV a)   = "(RV " ++ f a ++ ")"
              showRaw' _ (RA f t) = "(RA " ++ show f ++ " " ++ show t ++ ")"


liftShow :: SNat n -> (a -> String) -> (a :+: n) -> String
liftShow SZero f = f
liftShow (SSuc n) f = liftShow n (maybe "zero" (\x -> "(suc " ++ f x ++ ")"))

lambda = Λ

(→) :: Type -> Type -> Type
(→) = Fun

(.$) :: Term Raw a -> Term Raw a -> Term Raw a
(.$) (Λ Nil h ps) t = Λ Nil h (ps ++ [t])
(.$) (Λ (Cons n τ (τs :: Vec n' Type)) h ps ) (t :: Term Raw a)
    = Λ τs h ps >>= maybe t return

λ :: (Maybe String, Type) -> Term r (Suc a) -> Term r a
λ (n,τ) (Λ τs h ts) = Λ (Cons n τ τs) h ts

λ' :: Vec n Type -> Term r (a :+: n) -> Term r a
λ' Nil t = t
λ' (Cons n τ τs) t =  λ (n,τ) (λ' τs t)

instance Functor r => Functor (Term r) where
  fmap f (Λ Nil h ps) = Λ Nil (fmap f h) (fmap (fmap f) ps)
  fmap f (Λ (Cons n τ τs) h ps) = λ (n,τ) $ fmap (fmap f) (Λ τs h ps)

instance Monad (Term Raw) where
   return x = Λ Nil (RV x) []
   Λ Nil (RA c τ) ts >>= σ = Λ Nil (RA c τ) $ map (>>= σ) ts
   Λ Nil (RV ν) ts   >>= σ = foldl' (.$) (σ ν) $ map (>>= σ) ts
   Λ (Cons n τ τs) h ts  >>= σ = λ (n,τ) (Λ τs h ts >>= up σ)
     where up :: (a -> Term Raw b) -> (Suc a -> Term Raw (Suc b))
           up σ = maybe (return zero) (fmap suc . σ)

liftSubst :: SNat n -> (a  -> Term Raw b) -> a :+: n -> Term Raw (b :+: n)
liftSubst SZero σ = σ
liftSubst (SSuc n) (σ :: a -> Term Raw b) = liftSubst n (liftSubst' σ)
  where liftSubst' :: (a -> Term Raw b) -> Suc a -> Term Raw (Suc b)
        liftSubst' f = maybe (return Nothing) (fmap Just . f)

splitType :: Type -> ([Type], Type)
splitType (a `Fun` b) = first (a:) $ splitType b
splitType x           = ([],x)

unsplitType :: [Type] -> Type -> Type
unsplitType []     τ₀ = τ₀
unsplitType (τ:τs) τ₀ = τ → unsplitType τs τ₀

getType :: Term Typechecked a -> Type
getType (Λ τs (A x τ) _) = let (_,τ₀) = splitType τ
                            in unsplitType (toList τs) τ
getType (Λ τs (V x τ) _) = let (_,τ₀) = splitType τ
                            in unsplitType (toList τs) τ
targetType :: Type -> Type
targetType = snd . splitType

toRaw :: Term Typechecked a -> Term Raw a
toRaw (Λ τs (V c τ) ts) = Λ τs (RV c) $ map toRaw ts
toRaw (Λ τs (A c τ) ts) = Λ τs (RA c τ) $ map toRaw ts

inTerm :: f a -> Term f a
inTerm x = Λ Nil x []

containsFree :: Term Raw a -> Bool
containsFree (Λ τs (RA x τ) _) = True
containsFree (Λ τs h cs) = any containsFree cs

