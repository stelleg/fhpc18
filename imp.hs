{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{- Parallel IMP -}

type Name = String

data Expr a where
  Var :: Name -> Expr a
  Lit :: a -> Expr a
  (:-:) :: Expr Int -> Expr Int -> Expr Int
  (:+:) :: Expr Int -> Expr Int -> Expr Int
  (:*:) :: Expr Int -> Expr Int -> Expr Int
  (:/:) :: Expr Int -> Expr Int -> Expr Int
  Not :: Expr Bool -> Expr Bool 
  (:>:) :: Expr Int -> Expr Int -> Expr Bool

data Cmd where
  Skip :: Cmd
  Set :: Name -> Expr Int -> Cmd 
  If :: Expr Bool -> Cmd -> Cmd -> Cmd
  While :: Expr Bool -> Cmd -> Cmd
  Seq :: Cmd -> Cmd -> Cmd 
  Par :: Cmd -> Cmd -> Cmd

data Env = Nil | Map Name Int Env

data Eval :: Expr a -> Env -> a -> * where
  Eval Var e -> 

data Step :: Cmd -> Env -> Env -> * where
  SSkip :: Step Skip c c
  SSet :: Step (Set v e) c (Map v e c)


