{-# LANGUAGE DeriveFunctor #-}
module Gentzen.Equation where

data Equation a = (:=:) a a deriving (Functor, Show, Eq)

