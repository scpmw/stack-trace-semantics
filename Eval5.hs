module Eval5 where

import Syntax
import EvalTypes

import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer
import Data.Map (Map)
import qualified Data.Map as Map
import Text.PrettyPrint
import qualified Debug.Trace

-- -----------------------------------------------------------------------------

type E a = StateT (Heap,Costs,Int) (Writer [String]) a

trace :: String -> E ()
trace s = tell [s]

-- -----------------------------------------------------------------------------
-- Trying to get closer to what GHC actually does...

eval :: Stack -> Expr -> E (Stack,Expr)
eval ccs (EVar x) = eval_var ccs x

eval ccs (EInt i) =
   return (ccs, EInt i)

eval ccs (ELam x e) =
   return (ccs, ELam x e)

eval ccs (ELet (x,e1) e2) = do 
   trace ("Heap closure for " ++ x ++ ", Stack = " ++ showCCS ccs)
   modifyHeap (\h -> Map.insert x (ccs,e1) h)
   eval ccs e2

eval ccs (EPlus e1 e2) = do
   (_,EInt x) <- eval ccs e1
   (_,EInt y) <- eval ccs e2
   tick ccs
   return (ccs, EInt (x+y))

eval ccs (EApp f x) = do
   (lam_ccs, e) <- eval ccs f
   ELam y e' <- renameBound e Map.empty
   -- We combine cost-centres when the call is actually made
   let ccs' = funCall ccs lam_ccs
   trace ("Lam: " ++ show e ++ "\n" ++ show (ELam y e'))
   eval ccs' (subst y x e')

eval ccs (EPush cc e) =
   eval (pushCC cc ccs) e

eval_var ccs x = do
   r <- lookupHeap x
   case r of
	(ccs', EInt i) ->
	   return (ccs', EInt i)

	(ccsv, ELam y e) ->
	   return (ccsv, ELam y e)
           -- GHC doesn't touch the CCS when a variable gets
           -- referenced

	(ccs',e) -> do 
           trace ("Eval: " ++ x)
	   modifyHeap (\h -> Map.delete x h)
		-- delete it from the heap so we can get blackholes
	   (ccsv, v) <- eval ccs' e
           trace ("Update: " ++ x ++ ", Stack = " ++ showCCS ccsv)
	   update x (ccsv,v)
	   return (ccsv, v)

-- -----------------------------------------------------------------------------
-- Stack operations

funCall ccs_app ccs_lam
  = ccs_app `appendCCS` reverse ccs_lam'
  where
    (ccs_root, ccs_app', ccs_lam') = findCommonAncestor (reverse ccs_app) (reverse ccs_lam)

findCommonAncestor [] bs = ([],[],bs)
findCommonAncestor as [] = ([],as,[])
findCommonAncestor (a:as) (b:bs)
  | a == b    = (a:root, as', bs')
  | otherwise = ([], a:as, b:bs)
  where (root, as', bs') = findCommonAncestor as bs

appendCCS :: Stack -> Stack -> Stack
appendCCS ccs [] = ccs
appendCCS ccs ["CAF"] = ccs
appendCCS ccs (cc:ccs') = pushCC cc (appendCCS ccs ccs')

pushCC cc ccs
  | Just trunc <- findCC cc ccs = trunc
  | otherwise                   = cc:ccs

findCC cc [] = Nothing
findCC cc (cc':ccs)
  | cc == cc'  = Just (cc':ccs)
  | otherwise  = findCC cc ccs

-- -----------------------------------------------------------------------------
-- Misc.

tick ccs = modify (\ (h,c,i) -> (h, Map.insertWith (+) ccs 1 c, i))

modifyHeap f = modify (\(h,c,i) -> (f h, c, i))

lookupHeap :: Var -> E (Stack,Expr)
lookupHeap x = do
   (h,c,i) <- get
   case Map.lookup x h of
	Just z -> return z
	Nothing -> error ("unbound variable " ++ x)

update x val = modifyHeap (\h -> Map.insert x val h)

genSym :: E Int
genSym = do
  (h,c,i) <- get
  put (h,c,i+1)
  return i

isVal (ELam _ _) = True
isVal (EInt _)   = True
isVal _          = False

renameBound :: Expr -> Map Var Var -> E Expr
renameBound (EVar x) m =
  return (EVar (Map.findWithDefault x x m))
renameBound (ELam x e) m = do
  x' <- freshen x
  let m' = Map.insert x x' m
  ELam x' <$> renameBound e m'
renameBound (ELet (x,e) body) m = do
  e' <- renameBound e m
  x' <- freshen x
  let m' = Map.insert x x' m
  ELet (x',e') <$> renameBound body m'
renameBound (EPlus l r) m =
  EPlus <$> renameBound l m <*> renameBound r m
renameBound (EApp e x) m =
  EApp <$> renameBound e m <*> pure (Map.findWithDefault x x m)
renameBound (EPush l e) m =
  EPush l <$> renameBound e m
renameBound other m = return other

freshen :: Var -> E Var
freshen x = do
  j <- genSym
  return (takeWhile (/= '_') x ++ '_':show j)
