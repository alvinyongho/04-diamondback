{-# LANGUAGE FlexibleContexts #-}

--------------------------------------------------------------------------------
-- | This module contains the code for converting an `Expr` to a "A-Normal" form.
--------------------------------------------------------------------------------
module Language.Diamondback.Checker
  ( -- * Top-level Static Checker
    check

    -- * Error Constructors
  , errUnboundVar
  , errUnboundFun
  ) where

import           Control.Exception
import           Data.Monoid
import qualified Data.List          as L
import           Text.Printf        (printf)
import           Language.Diamondback.Types
import           Language.Diamondback.Utils

--------------------------------------------------------------------------------
check :: BareProgram -> BareProgram
--------------------------------------------------------------------------------
check p = case wellFormed p of
            [] -> p
            es -> throw es

-- | Map from function name to arity
type FunEnv = Env

--------------------------------------------------------------------------------
-- | `wellFormed p` returns the list of errors for a program `p`
--------------------------------------------------------------------------------
wellFormed :: BareProgram -> [UserError]
--------------------------------------------------------------------------------
wellFormed (Prog ds e) = duplicateFunErrors ds
                      ++ concatMap (wellFormedD fEnv) ds
                      ++ wellFormedE fEnv emptyEnv e
  where
    fEnv               = fromListEnv [(bindId f, length xs) | Decl f xs _ _ <- ds]

--------------------------------------------------------------------------------
-- | `wellFormedD fEnv vEnv d` returns the list of errors for a func-decl `d`
--------------------------------------------------------------------------------
wellFormedD :: FunEnv -> BareDecl -> [UserError]
wellFormedD fEnv (Decl _ xs e l) = duplicateParamErrors xs
                                ++ wellFormedE fEnv vEnv e
  where
    vEnv                         = addsEnv xs emptyEnv



-- arityErrors fEnv f l = condError (not (memberEnv f fEnv)) (errUnboundFun l f)
--------------------------------------------------------------------------------
-- | `wellFormedE vEnv e` returns the list of errors for an expression `e`
--------------------------------------------------------------------------------
wellFormedE :: FunEnv -> Env -> Bare -> [UserError]
wellFormedE fEnv env e = go env e
  where
    gos                       = concatMap . go
    go _    (Boolean {})      = []
    go _    (Number  n     l) = largeNumErrors n l
                             ++ []
    go vEnv (Id      x     l) = unboundVarErrors vEnv x l
    go vEnv (Prim1 _ e     _) = go  vEnv e
    go vEnv (Prim2 _ e1 e2 _) = gos vEnv [e1, e2]
    go vEnv (If   e1 e2 e3 _) = gos vEnv [e1, e2, e3]
    go vEnv (Let x e1 e2   l) = shadowVarErrors vEnv (bindId x) l
                             ++ go vEnv e1
                             ++ go (addEnv x vEnv) e2
    go vEnv (App f es      l) = unboundFunErrors fEnv f l
                            --  ++ arityErrors fEnv f es l
                             ++ gos vEnv es


addsEnv :: [BareBind] -> Env -> Env
addsEnv xs env = L.foldl' (\e x -> addEnv x e) env xs

--------------------------------------------------------------------------------
-- | Error Checkers: In each case, return an empty list if no errors.
--------------------------------------------------------------------------------
duplicateFunErrors :: [BareDecl] -> [UserError]
duplicateFunErrors
  = fmap errDupFun
  . concat
  . dupBy (bindId . fName)


duplicateParamErrors :: [BareBind] -> [UserError]
duplicateParamErrors xs
  = fmap (errDupParam . head)
  . dupBy bindId
  $ xs



-- arityErrors fEnv xs l = condError((True)(errCallArity l))



-- | `maxInt` is the largest number you can represent with 31 bits (accounting for sign
--    and the tag bit.

maxInt :: Integer
maxInt = 1073741824

condError :: Bool -> UserError -> [UserError]
condError True u = [u]
condError False _ = []

shadowVarErrors :: Env -> Id -> SourceSpan -> [UserError]
shadowVarErrors vEnv x l =
  condError ((memberEnv x vEnv)) (errShadowVar l x)

unboundVarErrors :: Env -> Id -> SourceSpan -> [UserError]
unboundVarErrors vEnv x l =
  condError (not (memberEnv x vEnv)) (errUnboundVar l x)

unboundFunErrors :: FunEnv -> Id -> SourceSpan -> [UserError]
unboundFunErrors fEnv f l =
  condError (not (memberEnv f fEnv)) (errUnboundFun l f)


-- arityErrors :: FunEnv -> Id -> SourceSpan -> [UserError]
-- arityErrors fEnv f es l =
--   condError (not ((getLength fEnv) == length es)) (errCallArity l f)

largeNumErrors :: Integer -> SourceSpan -> [UserError]
largeNumErrors n l =
  condError (abs(fromIntegral (n)) >  (maxInt))
            (errLargeNum l n)

--------------------------------------------------------------------------------
-- | Error Constructors: Use these functions to construct `UserError` values
--   when the corresponding situation arises. e.g see how `errDupFun` is used.
--------------------------------------------------------------------------------

errDupFun :: (Located (Bind a)) => Decl a -> UserError
errDupFun d = mkError (printf "duplicate function '%s'" (pprint f))    (sourceSpan f) where f = fName d

errDupParam :: (Located (Bind a)) => Bind a -> UserError
errDupParam x = mkError (printf "Duplicate parameter '%s'" (bindId x)) (sourceSpan x)

errDupBind :: (Located (Bind a)) => Bind a -> UserError
errDupBind x = mkError (printf "Shadow binding '%s'" (bindId x))      (sourceSpan x)

errLargeNum :: SourceSpan -> Integer -> UserError
errLargeNum   l n = mkError (printf "Number '%d' is too large" n) l

errUnboundVar :: SourceSpan -> Id -> UserError
errUnboundVar l x = mkError (printf "Unbound variable '%s'" x) l

errShadowVar :: SourceSpan -> Id -> UserError
errShadowVar l x = mkError (printf "Shadow binding variable '%s'" x) l

errUnboundFun :: SourceSpan -> Id -> UserError
errUnboundFun l f = mkError (printf "Function '%s' is not defined" f) l

errCallArity :: SourceSpan -> Id -> UserError
errCallArity  l f = mkError (printf "Wrong arity of arguments at call of %s" f) l
