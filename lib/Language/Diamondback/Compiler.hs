{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

--------------------------------------------------------------------------------
-- | The entry point for the compiler: a function that takes a Text
--   representation of the source and returns a (Text) representation
--   of the assembly-program string representing the compiled version
--------------------------------------------------------------------------------

module Language.Diamondback.Compiler ( compiler, compile ) where

import           Data.Monoid
import           Control.Arrow                    ((>>>))
import           Text.Printf                     (printf)
import           Prelude                  hiding (compare)
import           Control.Monad                   (void)
import           Data.Maybe
import           Data.Bits                       (shift)
import           Language.Diamondback.Types      hiding (Tag)
import           Language.Diamondback.Parser     (parse)
import           Language.Diamondback.Checker    (check, errUnboundVar)
import           Language.Diamondback.Normalizer (anormal)
import           Language.Diamondback.Label
import           Language.Diamondback.Asm        (asm)


--------------------------------------------------------------------------------
compiler :: FilePath -> Text -> Text
--------------------------------------------------------------------------------
compiler f = parse f >>> check >>> anormal >>> tag >>> tails >>> compile >>> asm


--------------------------------------------------------------------------------
-- | The compilation (code generation) works with AST nodes labeled by @Ann@
--------------------------------------------------------------------------------
type Ann   = ((SourceSpan, Int), Bool)
type AExp  = AnfExpr Ann
type IExp  = ImmExpr Ann
type ABind = Bind    Ann
type ADcl  = Decl    Ann
type APgm  = Program Ann

instance Located Ann where
  sourceSpan = fst . fst

instance Located a => Located (Expr a) where
  sourceSpan = sourceSpan . getLabel

annTag :: Ann -> Int
annTag = snd . fst

annTail :: Ann -> Bool
annTail = snd


--------------------------------------------------------------------------------
compile :: APgm -> [Instruction]
--------------------------------------------------------------------------------
compile (Prog ds e) = compileBody emptyEnv e
                   <> concatMap compileDecl ds

compileDecl :: ADcl -> [Instruction]
compileDecl (Decl f xs e l) = ILabel (DefFun (bindId f))
                            : compileBody (paramsEnv xs) e
                            -- where
                              -- env = fromListEnv (zip (bindId <$> xs) [-2,-3..])

paramsEnv :: [Bind a] -> Env
paramsEnv xs = fromListEnv (zip (bindId <$> xs) [-2, -3..])

-- compileBody :: Env -> AExp -> [Instruction]
compileBody env e = funInstrs (countVars e) (compileEnv env e)

-- | @funInstrs n body@ returns the instructions of `body` wrapped
--   with code that sets up the stack (by allocating space for n local vars)
--   and restores the callees stack prior to return.

funInstrs :: Int -> [Instruction] -> [Instruction]
funInstrs n instrs
  = funEntry n
 ++ instrs
 ++ funExit
 ++ [IRet]

-- FILL: insert instructions for setting up stack for `n` local vars
funEntry :: Int -> [Instruction]
funEntry n = [ IPush (Reg EBP)
             , IMov (Reg EBP) (Reg ESP)
             , ISub (Reg ESP) (Const (4 * n))]

-- FILL: clean up stack & labels for jumping to error
funExit :: [Instruction]
funExit = [ IMov (Reg ESP) (Reg EBP)
          , IPop (Reg EBP)
          ]
          -- , IRet ]

--------------------------------------------------------------------------------
-- | @countVars e@ returns the maximum stack-size needed to evaluate e,
--   which is the maximum number of let-binds in scope at any point in e.
--------------------------------------------------------------------------------
countVars :: AnfExpr a -> Int
--------------------------------------------------------------------------------
countVars (Let _ e b _)  = max (countVars e) (1 + countVars b)
countVars (If v e1 e2 _) = maximum [countVars v, countVars e1, countVars e2]
countVars _              = 0

--------------------------------------------------------------------------------
compileEnv :: Env -> AExp -> [Instruction]
--------------------------------------------------------------------------------
-- compileEnv env e = error "TBD:compileEnv"

tailcall :: Label -> [Arg] -> [Instruction]
tailcall f args
  = copyArgs args
  ++ funExit
  ++ [IJmp f] -- jump to start


copyArgs :: [Arg] -> [Instruction]
copyArgs = concat . zipWith copyArg [-2, -3..]
  where
    copyArg i a = [ IMov (Reg EAX) a
                  , IMov (stackVar i) (Reg EAX)
                  ]

compileEnv env (App f vs l)
  | annTail l = tailcall (DefFun f) (param env <$> vs)
  | otherwise = call (DefFun f) [param env v | v <- vs]

compileEnv env v@Number {}       = [ IMov (Reg EAX) (immArg env v) ]

compileEnv env v@Boolean {}      = [ IMov (Reg EAX) (immArg env v)  ]

compileEnv env v@Id {}           = [ compileImm env v  ]

compileEnv env e@Let {}          = is ++ compileEnv env' body
  where
    (env', is)                   = compileBinds env [] binds
    (binds, body)                = exprBinds e

compileEnv env (Prim1 o v l)     = compilePrim1 l env o v

compileEnv env (Prim2 o v1 v2 l) = compilePrim2 l env o v1 v2

compileEnv env (If v e1 e2 l)    = compileIf l env v e1 e2


compileImm :: Env -> IExp -> Instruction
compileImm env v = IMov (Reg EAX) (immArg env v)

compileBinds :: Env -> [Instruction] -> [(ABind, AExp)] -> (Env, [Instruction])
compileBinds env is []     = (env, is)
compileBinds env is (b:bs) = compileBinds env' (is <> is') bs
  where
    (env', is')            = compileBind env b

compileBind :: Env -> (ABind, AExp) -> (Env, [Instruction])
compileBind env (x, e) = (env', is)
  where
    is                 = compileEnv env e
                      <> [IMov (stackVar i) (Reg EAX)]
    (i, env')          = pushEnv x env


compilePrim1 :: Ann -> Env -> Prim1 -> IExp -> [Instruction]
compilePrim1 l env Add1 v = compilePrim2 l env Plus v (Number 1 l)
compilePrim1 l env Sub1 v = compilePrim2 l env Minus v (Number 1 l)

compilePrim1 l env Print v = call (Builtin "print") [param env v]
                              -- clear the arguments by adding 4 * numArgs which is 2


compilePrim1 l env IsNum v = isType l TNumber env v

compilePrim1 l env IsBool v = isType l TBoolean env v


-- | TBD: Implement code for `Prim2` with appropriate type checking
compilePrim2 :: Ann -> Env -> Prim2 -> IExp -> IExp -> [Instruction]
-- compilePrim2 l env op = error "TBD:compilePrim2"
compilePrim2 l env Plus v1 v2 =
                                assertType TNumber env v1
                             ++ assertType TNumber env v2
                             ++ [ IMov (Reg EAX) (immArg env v1)
                                , IAdd (Reg EAX) (immArg env v2)
                                ]
                                -- ++ [ ICmp (Reg EAX) (Const 0)
                                --   ,  IJo  (DynamicErr ArithOverflow)]
                                ++ [IJo  (DynamicErr ArithOverflow)]

compilePrim2 l env Minus v1 v2 =
                                 assertType TNumber env v1
                              ++ assertType TNumber env v2
                              ++ [ IMov (Reg EAX) (immArg env v1)
                                 , ISub (Reg EAX) (immArg env v2)
                                 ]
                              -- ++ [ ICmp (Reg EAX) (Const 0)
                              --     ,IJo  (DynamicErr ArithOverflow)]
                              ++ [IJo  (DynamicErr ArithOverflow)]

compilePrim2 l env Times v1 v2 =
                                 assertType TNumber env v1
                              ++ assertType TNumber env v2
                              ++ [ IMov (Reg EAX) (immArg env v1)
                                 , IMul (Reg EAX) (immArg env v2)
                                 , ISar (Reg EAX) (Const 1)
                                 , IJo  (DynamicErr ArithOverflow)
                                 ]
                                --  ++ [ ICmp (Reg EAX) (Const 0)


compilePrim2 l env Equal v1 v2
  = compileCmp (annTag l) env IJe v1 v2

compilePrim2 l env Greater v1 v2
  = compileCmp (annTag l) env IJg v1 v2

compilePrim2 l env Less v1 v2
  = compileCmp (annTag l) env IJl v1 v2

compileCmp l env jop v1 v2 =
   assertType TNumber env v1
     ++ assertType TNumber env v2
     ++
  [ IMov (Reg EAX) (immArg env v1)
  , ICmp (Reg EAX) (immArg env v2)
  , jop  lTrue
  , IMov (Reg EAX) (repr False)
  , IJmp lExit
  , ILabel lTrue
  , IMov (Reg EAX) (repr True)
  , ILabel lExit
  ]
  where
    lTrue = BranchTrue l
    lExit = BranchDone l



-- | TBD: Implement code for `If` with appropriate type checking
compileIf :: Ann -> Env -> IExp -> AExp -> AExp -> [Instruction]
compileIf l env v e1 e2 =
    -- compilePrim1 l env IsBool v++

    assertType TBoolean env v ++
    compileEnv env v ++         -- compile the condition
    [ ICmp (Reg EAX) (HexConst 0x7fffffff)      -- check the condition is false
    , IJne (BranchTrue  (annTag l))    -- if the condition is not false then it must be true so jump to BranchTrue
    ]
    ++ compileEnv env e2 ++     -- since the condition is false (not skipped) then compute the False expression
    [ IJmp (BranchDone (annTag l))     -- computation is done so skip to BranchDone label
    , ILabel (BranchTrue (annTag l))   -- Branch True label
    ]
    ++ compileEnv env e1 ++      -- Computations for the true expression
    [ ILabel (BranchDone (annTag l)) ] -- BranchDone label (where False expression can skip to when done, and following true)


assertType :: Ty -> Env -> IExp -> [Instruction]
assertType ty env v =
  [ IMov (Reg EAX) (immArg env v)
  , IMov (Reg EBX) (Reg EAX)
  , IAnd (Reg EBX) (HexConst 0x00000001)
  , ICmp (Reg EBX) (tagValue ty)
  , IJne (DynamicErr (TypeError ty))
  ]


isType :: Ann -> Ty -> Env -> IExp -> [Instruction]
isType l ty env v =
  [ IMov (Reg EAX) (immArg env v)
  , IMov (Reg EBX) (Reg EAX)
  , IAnd (Reg EBX) (HexConst 0x00000001)
  , ICmp (Reg EBX) (tagValue ty)
  , IJe  lTrue
  , IMov (Reg EAX) (repr False)
  , IJmp lExit
  , ILabel lTrue
  , IMov (Reg EAX) (repr True)
  , ILabel lExit
  ]
  where
    lTrue = BranchTrue (annTag l)
    lExit = BranchDone (annTag l)



tagValue :: Ty -> Arg
tagValue TNumber  = HexConst 0x00000000
tagValue TBoolean = HexConst 0x00000001




immArg :: Env -> IExp -> Arg
immArg _   (Number n _)  = repr n
immArg _   (Boolean b _) = repr b
immArg env e@(Id x _)    = stackVar (fromMaybe err (lookupEnv x env))
  where
    err                  = abort (errUnboundVar (sourceSpan e) x)
immArg _   e             = panic msg (sourceSpan e)
  where
    msg                  = "Unexpected non-immExpr in immArg: " <> show (void e)

stackVar :: Int -> Arg
stackVar i = RegOffset (-4 * i) EBP


call :: Label -> [Arg] -> [Instruction]
call f args =
  pushArgs args            -- Push in the args in reverse order
  ++ [ICall f]
  ++ popArgs (length args) -- Reset the ESP


pushArgs :: [Arg] -> [Instruction]
pushArgs args =
  ISub (Reg ESP) (Const (4*n))
  : [ IPush a | a <- reverse args ]
  where n = length args

popArgs :: Int -> [Instruction]
popArgs n = [ IAdd (Reg ESP) (Const (4*n)) ]

param :: Env -> IExp -> Arg
param env v = Sized DWordPtr (immArg env v)

compareCheck env (Just t) v1 v2
 = assertType env v1 t
 <> assertType env v2 t

-- compareVal :: Ann -> Env -> COp -> IExp -> IExp -> [Instruction]
-- compareVal l env j v1 v2
--   = IMov (Reg EAX) (immArg env v1)
--   : IMov (Reg EBX) (immArg env v2)
--   : ICmp (Reg EAX) (Reg EBX)
--   : boolBranch l j

assign :: (Repr a) => Reg -> a -> Instruction
assign r v = IMov (Reg r) (repr v)



--------------------------------------------------------------------------------
-- | Representing Values
--------------------------------------------------------------------------------

class Repr a where
  repr :: a -> Arg

instance Repr Bool where
  repr True  = HexConst 0xffffffff
  repr False = HexConst 0x7fffffff

instance Repr Int where
  repr n = Const (fromIntegral (shift n 1))

instance Repr Integer where
  repr n = Const (fromIntegral (shift n 1))

typeTag :: Ty -> Arg
typeTag TNumber   = HexConst 0x00000000
typeTag TBoolean  = HexConst 0x7fffffff

typeMask :: Ty -> Arg
typeMask TNumber  = HexConst 0x00000001
typeMask TBoolean = HexConst 0x7fffffff
