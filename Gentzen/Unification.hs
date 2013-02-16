{-# LANGUAGE TypeOperators, GADTs, ScopedTypeVariables, GeneralizedNewtypeDeriving #-}
module Gentzen.Unification where

import Gentzen.Equation
import Gentzen.Term
import Gentzen.Vector (Vec (..))
import qualified Gentzen.Vector as V
import Gentzen.Typechecker
import Gentzen.TypeLevel
import Gentzen.TypeEnv
import qualified Gentzen.FreeSubst as S
import Gentzen.FreeSubst (FreeSubst)

import Control.Applicative
import Data.Foldable
import Data.Traversable
import Control.Monad.Error hiding (forM, mapM, sequence)
import Control.Monad.State hiding (forM, mapM, sequence)
import Data.Monoid
import Data.Either
import Data.List(intersect)
import Control.Arrow

import Prelude hiding (concat, mapM, sequence, all, elem)

simpl :: (Eq a) => Equation (Term Typechecked a) -> Maybe [Equation (Term Typechecked a)]
simpl (Λ _ (A c τ) _       :=: Λ _ (A c' τ') _    ) | c == c' && τ == τ' = Just []
simpl eq@(Λ _ (A {}) _     :=: _                  ) = Just [eq]
simpl eq@(_                :=: Λ _ (A {}) _       ) = Just [eq]
simpl (Λ Nil (V ν₁ τ₁) ts₁ :=: Λ Nil (V ν₂ τ₂) ts₂) | ν₁ == ν₂ = Just $ zipWith (:=:) ts₁ ts₂
simpl (Λ Nil (V ν₁ τ₁) ts₁ :=: Λ Nil (V ν₂ τ₂) ts₂) | ν₁ == ν₂ = Just $ zipWith (:=:) ts₁ ts₂
simpl (Λ (Cons n₁ τ₁ τs₁) h₁ ts₁ :=: Λ (Cons n₂ τ₂ τs₂) h₂ ts₂) | τ₁ == τ₂
   = let e = Λ τs₁ h₁ ts₁ :=: Λ τs₂ h₂ ts₂
      in map (fmap (λ (n₁, τ₁))) <$> simpl e
simpl _                                                        = Nothing

data UnificationError = OtherUniError String
                      | TypeError TypeError
                      | CannotUnify String String
               deriving Show

instance Error UnificationError where
  strMsg = OtherUniError

newtype UnificationM a = UniM { runUniM :: StateT Int (Either UnificationError) a }
              deriving ( Monad
                       , Functor
                       , Applicative
                       , Alternative
                       , MonadPlus
                       , MonadError UnificationError
                       , MonadState Int
                       )

freshName :: Type -> UnificationM (Raw a)
freshName τ = do modify (+1)
                 (\c -> RA c τ) . show <$> get

allTV :: SNat n -> Vec m (Raw a) -> Vec (n `NatPlus` m) (Raw (a :+: n))
allTV SZero    l = l
allTV (SSuc n) l =  allTV n (Cons Nothing (RV zero) (fmap (fmap suc) l))

imitate :: Equation (Term Typechecked a) -> UnificationM (FreeSubst a)
imitate (Λ as (A x τ) e¹s :=: Λ as' (V ν τ') e²s :: Equation (Term Typechecked a))
   | Just Refl      <- V.eq as as'
   , n              <- V.length as'
   , Just (ν' :: a) <- extract n ν
   , (τs, τ₀)       <- splitType τ
   , ExI (Flip τsV) <- V.fromList τs
   , p₁             <- V.length τsV
   , (τs', τ₀')     <- splitType τ'
   , hτs            <- map (unsplitType τs) τs'
   = do ls <- forM hτs $ (flip newUniVar p₁)
        return $ S.singleton (x,τ) (Λ τsV (RV $ upN p₁ ν') ls)
  where newUniVar :: Type -> SNat m -> UnificationM (Term Raw (a :+: m))
        newUniVar hτ n = do h <- freshName hτ
                            return $ Λ Nil h (map inTerm $ toList $ allTV' n Nil)
        allTV' :: SNat n -> (Vec m (Raw a)) -> Vec (n `NatPlus` m) (Raw (a :+: n))
        allTV' = allTV
imitate (Λ as' (V ν τ') e²s :=: Λ as (A x τ) e¹s)
   = imitate $ Λ as (A x τ) e¹s :=: Λ as' (V ν τ') e²s
imitate _ = return mempty

project :: Equation (Term Typechecked a) -> UnificationM (FreeSubst a)
project (Λ as' (V ν τ') e²s :=: Λ as (A x τ) e¹s)
   = project $ Λ as (A x τ) e¹s :=: Λ as' (V ν τ') e²s
project (Λ as (A x τ) e¹s :=: Λ as' (V {}) _ :: Equation (Term Typechecked a))
   | Just Refl      <- V.eq as as'
   , (τs, τ₀)       <- splitType τ
   , ExI (Flip τ¹s) <- V.fromList $ map getType e¹s
   , len            <- V.length τ¹s
   , Refl           <- plusZero len
   , allVars        <- allTV' len Nil
   , vec            <- V.zip τ¹s allVars
   = fmap (mconcat . V.toList) $ forM vec $ \(τ¹, i) ->
        let (τs', τ₀') = splitType τ¹
            hτs  = map (unsplitType $ V.toList τ¹s) τs'
        in if (τ₀' == τ₀) then do
             ls <- forM hτs $ (flip (newUniVar len) $ map (\x -> Λ Nil x []) $ V.toList allVars)
             return $ S.singleton (x, τ) (Λ τ¹s i ls)
           else return mempty

 where allTV' :: SNat n -> Vec m (Raw a) -> Vec (n `NatPlus` m) (Raw (a :+: n))
       allTV' = allTV
       newUniVar :: SNat n -> Type -> [Term Raw (a :+: n)] -> UnificationM (Term Raw (a :+: n))
       newUniVar _  hτ n = do h <- freshName hτ
                              return $ Λ Nil h n

match :: Show a => Equation (Term Typechecked a) -> UnificationM (FreeSubst a)
match e = guardNotEmpty =<< ((<>) <$> imitate e <*> project e)
   where guardNotEmpty x | S.null x, a :=: b <- e = throwError $ CannotUnify (show a) (show b)
         guardNotEmpty x = return x

type UnificationProblem a = [Equation (Term Typechecked a)]
type Ξ a = UnificationProblem a

data Classification a = Classify { flexFlex  :: UnificationProblem a
                                 , flexRigid :: UnificationProblem a
                                 , rigidRigid :: UnificationProblem a
                                 }

instance Monoid (Classification a) where
  mempty = Classify [] [] []
  mappend (Classify a b c) (Classify a' b' c') = Classify (a ++ a') (b ++ b') (c ++ c')

classify :: UnificationProblem a -> Classification a
classify = foldMap classify'
  where classify' eq@(Λ _ (A {}) _ :=: Λ _ (A {}) _) = Classify [eq] [] []
        classify' eq@(Λ _ (A {}) _ :=: Λ _ (V {}) _) = Classify [] [eq] []
        classify' eq@(Λ _ (V {}) _ :=: Λ _ (A {}) _) = Classify [] [eq] []
        classify' eq@(Λ _ (V {}) _ :=: Λ _ (V {}) _) = Classify [] [] [eq]

data UnificationTree a = Success (UnificationProblem a)
                       | Failure UnificationError
                       | Node [(FreeSubst a, UnificationTree a)]
                       deriving Show

tcmToUnificationM :: TCM a -> UnificationM a
tcmToUnificationM = either (throwError . TypeError) return . runTCM




substProblem :: Γ a -> UnificationProblem a -> FreeSubst a -> UnificationM (UnificationProblem a)
substProblem envΓ p σ = mapM substU' p
  where substU' (a :=: b) = tcmToUnificationM $ typecheckEq envΓ (subst'' σ a :=: subst'' σ b)
        subst'' :: FreeSubst a -> Term Typechecked a -> Term Raw a
        subst'' σ = S.freeSubst σ . toRaw

declassify :: Classification a -> UnificationProblem a
declassify (Classify ff fr rr) = ff ++ fr ++ rr

tree :: (Show a, Eq a) => Γ a -> Classification a -> UnificationM (UnificationTree a)
tree envΓ p@(Classify ff [] []) = return (Success ff)
tree envΓ p@(Classify ff fr []) = do σs <- concat . (:[]) <$> mapM match fr
                                     ps <- mapM (substProblem envΓ $ declassify p) σs
                                     ts <- mapM (treeOrFail . classify) ps
                                     return $ Node $ zip σs ts
     where treeOrFail x = tree envΓ x `catchError` (return . Failure)
tree envΓ p@(Classify ff fr rr) = case fmap concat $ sequence $ map simpl rr
                                    of Just rr' -> treeOrFail $ (Classify ff fr []) <> classify rr'
                                       Nothing  -> return . Failure $ OtherUniError (show rr)
     where treeOrFail x = tree envΓ x `catchError` (return . Failure)


type Traversal a = [(FreeSubst a, UnificationTree a)]
type Solution a =  (FreeSubst a, UnificationProblem a)

step :: Traversal a -> ([Solution a], Traversal a)
step st = fmap concat $ partitionEithers $ map (uncurry $ step') st

step' :: FreeSubst a -> UnificationTree a -> Either (Solution a) (Traversal a)
step' σ (Success ρ) = Left (σ, ρ)
step' σ (Failure _) = Right []
step' σ (Node σs) = Right $ map (first (σ <>)) σs

steps :: Traversal a -> [Solution a]
steps t = let (as,t') = step t
           in if null t' then as else as ++ steps t'

checkSolution :: (Eq a) => UnificationProblem a -> UnificationProblem a -> Bool
checkSolution = checkSolution' . classify

checkSolution' :: (Eq a) => Classification a -> UnificationProblem a -> Bool
checkSolution' (Classify ff [] []) rem = all (`elem` rem) ff
checkSolution' (Classify ff [] rr) rem = case fmap concat $ sequence $ map simpl rr
                      of Just rr' -> flip checkSolution' rem $ Classify ff [] [] <> classify rr'
                         Nothing  -> False
checkSolution' (Classify ff fr []) _   = False


