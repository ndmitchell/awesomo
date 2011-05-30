{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import qualified Core as C
import Control.Arrow
import Control.Monad.State
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import System.Environment
import System.Cmd
import System.Directory
import System.FilePath
import Data.Generics.Uniplate.Data
import Data.Data


main = do
    xs <- getArgs
    forM_ xs $ \x -> do
        exp <- C.parseFile x
        let prg = toGraph exp
        createDirectoryIfMissing True $ dropExtension x
        let path = dropExtension x ++ "/"
        forM_ (zip [0..20] $ prg : evals prg) $ \(i,p) -> writeDot (path ++ show i) $ gc p
        writeDot (path ++ "simp") $ gc $ simplify prg


writeDot file prg = do
    writeFile (file ++ ".dot") $ toDot prg
    system $ "\"C:\\Program Files\\Graphviz2.22\\bin\\dot.exe\" -Tpng " ++ file ++ ".dot -o" ++ file ++ ".png"


---------------------------------------------------------------------
-- TYPE

type Var = String
type Con = String
newtype Ptr = Ptr {fromPtr :: Integer} deriving (Eq,Ord,Data,Typeable)
instance Show Ptr where show (Ptr x) = show x

data Exp
    = Lam Ptr Ptr
    | App Ptr Ptr
    | Var Var
    | Push Ptr [(Ptr, Ptr)]
    | Con Con [Ptr]
    | Case Ptr [(Con, [Ptr], Ptr)]
      deriving (Show,Data,Typeable)

data Prog = Prog {progUnique :: Ptr, progBind :: [(Ptr,Exp)], progRoot :: Ptr}
            deriving (Show,Data,Typeable)

---------------------------------------------------------------------
-- MONAD

type ProgM = State Prog

progM :: Prog -> ProgM () -> Prog
progM = flip execState

getRoot :: ProgM Ptr
getRoot = gets progRoot

setRoot :: Ptr -> ProgM ()
setRoot r = modify $ \s -> s{progRoot=r}

newPtr :: ProgM Ptr
newPtr = do
    s <- get
    put s{progUnique = Ptr $ 1 + fromPtr (progUnique s)}
    return $ progUnique s

addExp :: Ptr -> Exp -> ProgM ()
addExp p x = modify $ \s -> s{progBind = (p,x) : progBind s}

add :: Exp -> ProgM Ptr
add e = do
    p <- newPtr
    addExp p e
    return p


---------------------------------------------------------------------
-- TO GRAPH

toGraph :: C.Exp -> Prog
toGraph x = progM (Prog (Ptr 0) [] (Ptr 0)) $ setRoot =<< toGraphExp [] x


toGraphExp :: [(Var, Ptr)] -> C.Exp -> ProgM Ptr
toGraphExp env (C.Let binds x) = do
    ps <- replicateM (length binds) newPtr
    let env2 = zip (map fst binds) ps ++ env
    es <- mapM (toGraphExp env2) $ map snd binds
    zipWithM_ addExp ps $ map (`Push` []) es
    return $ lookup_ x env2

toGraphExp env (C.Lam x e) = do
    p <- add $ Var x
    e <- toGraphExp ((x,p) : env) e
    add $ Lam p e

toGraphExp env (C.App x ys) = foldM f (lookup_ x env) $ map (`lookup_` env) ys
    where f a b = add $ App a b

toGraphExp env (C.Con c xs) = add $ Con c $ map (`lookup_` env) xs 

toGraphExp env (C.Case x ps) = do
    alts <- forM ps $ \(C.Con c vs,x) -> do
        ps <- mapM (add . Var) vs
        x <- toGraphExp (zip vs ps ++ env) x
        return (c,ps,x)
    add $ Case (lookup_ x env) alts


---------------------------------------------------------------------
-- TO DOT

toDot :: Prog -> String
toDot (Prog _ bind x) = unlines $ ["digraph g {","start -> " ++ show x ++ ";"] ++ map f bind ++ ["}"]
    where
        f (p, Lam a b) = show p ++ "[label=\"%\"];" ++ show p ++ "->" ++ show a ++ "[style=dotted];" ++ show p ++ "->" ++ show b ++ ";"
        f (p, App a b) = show p ++ "[label=\"$\"];" ++ show p ++ "->" ++ show a ++ ";" ++ show p ++ "->" ++ show b ++ "[style=dotted];"
        f (p, Var a) = show p ++ "[shape=box label=" ++ show a ++ "];"
        f (p, Push a []) = show p ++ "[shape=box label=\"\"];" ++ show p ++ "->" ++ show a ++ ";"
        f (p, Push a bs) = show p ++ "[shape=box label=\"\"];_" ++ show p ++ "[label=\"\"];" ++
                           show p ++ "->_" ++ show p ++ ";_" ++ show p ++ "->" ++ show a ++ ";" ++
                           concat [show x ++ "->_" ++ show p ++ "[style=dashed label=" ++ show i ++ "];_" ++ show p ++ "->" ++ show y ++ "[style=dashed label=" ++ show i ++ "]" | (i,(x,y)) <- zip [1..] bs]
        f (p, Con c cs) = show p ++ "[label=" ++ show c ++ "];" ++
                          concat [show p ++ "->" ++ show c ++ "[label=" ++ show i ++ "];" | (i,c) <- zip [1..] cs]
        f (p, Case a b) = show p ++ "[label=case];" ++ show p ++ "->" ++ show a ++ ";" ++
                          concat [c ++ "_" ++ show p ++ "[label=" ++ c ++ "];" ++ show p ++ "->" ++ c ++ "_" ++ show p ++ "[style=dotted];" ++ c ++ "_" ++ show p ++ "->" ++ show b ++ ";" ++
                            concat [c ++ "_" ++ show p ++ "->" ++ show a ++ "[style=dotted label=" ++ show i ++ "];" | (i,a) <- zip [1..] as]
                            | (c,as,b) <- b]


---------------------------------------------------------------------
-- GC

gc :: Prog -> Prog
gc (Prog u bind x) = Prog u (filter (flip Set.member reach . fst) bind) x
    where
        reach = f Set.empty [x]
    
        f seen (t:odo) | t `Set.member` seen = f seen odo
                       | otherwise = f (Set.insert t seen) $ odo ++ universeBi (lookup_ t bind)
        f seen [] = seen


---------------------------------------------------------------------
-- EVALUATION

evals :: Prog -> [Prog]
evals = unfoldr $ fmap (\x -> (x,x)) . eval


-- | Like step, but if you are at an outer constructor, evaluate the constructor fields
eval :: Prog -> Maybe Prog
eval = step


-- | Return either the one step evaluation, or Nothing if it cannot evaluate further
step :: Prog -> Maybe Prog
step (Prog u bind p) = case lookup_ p bind of
    Push a [] -> Just $ Prog u bind a
    Push a bs | (n:ew, Prog u bind p) <- dupe (a:map fst bs) $ Prog u bind p -> Just $ repoint (zip ew $ map snd bs) $ Prog u bind n
    App a b | Lam c d <- lookup_ a bind -> Just $ Prog u ((p,Push d [(c,b)]) : remove p bind) p
            | Just (Prog u2 bind2 p2) <- step $ Prog u bind a -> Just $ Prog u2 ((p,App p2 b) : remove p bind2) p
    Case a b | Con c d <- lookup_ a bind, (_,ps,bod):_ <- filter ((==) c . fst3) b -> Nothing
             | Just (Prog u2 bind2 p2) <- step $ Prog u bind a -> Just $ Prog u2 ((p,Case p2 b) : remove p bind2) p
    _ -> Nothing


dupe :: [Ptr] -> Prog -> ([Ptr], Prog)
dupe ps (Prog u bind p) = (map i ps, Prog (i u) (bind ++ map f bind) p)
    where
        i x = Ptr $ fromPtr u + 1 + fromPtr x

        f (a, b) = (i a, g b)
        g (Lam a b) = Lam (i a) (i b)
        g (App a b) = App (i a) (i b)
        g (Var x) = Var x
        g (Push a bs) = Push (i a) (map (\(a,b) -> (i a, i b)) bs)
        g (Con x as) = Con x (map i as)
        g (Case a bs) = Case (i a) [(a,map i b,i c) | (a,b,c) <- bs]


repoint :: [(Ptr,Ptr)] -> Prog -> Prog
repoint env (Prog a b c) = Prog a (map f b) c
    where
        f (p, Var x) | Just p2 <- lookup p env = (p, Push p2 [])
        f x = x


---------------------------------------------------------------------
-- SIMPLIFY

simplify :: Prog -> Prog
simplify x = applyLambda $ emptyPush $ dullPush $ applyLambda $ applyLambda $ applyLambda $ applyLambda $ applyLambda $ emptyPush $ emptyPush x

dullPush :: Prog -> Prog
dullPush (Prog a b c) = Prog a (map (second f) b) c
    where
        f (Push p xs) = Push p $ filter (\(a,b) -> a /= b) xs
        f x = x

emptyPush :: Prog -> Prog
emptyPush (Prog a b c) = rename env $ Prog a b c
    where env = [(p1,p2) | (p1,Push p2 []) <- b]


applyLambda :: Prog -> Prog
applyLambda (Prog u bind start) = Prog u (env ++ removes (map fst env) bind) start
    where env = [(p,Push d [(c,b)]) | (p,App a b) <- bind, Lam c d <- [lookup_ a bind]]


rename :: [(Ptr,Ptr)] -> Prog -> Prog
rename env (Prog a b c) = Prog a (map (second $ transformBi f) b) (f c)
    where f x = fromMaybe x $ lookup x env


---------------------------------------------------------------------
-- UTILITY

lookup_ x y = fromJust $ lookup x y

remove x ys = filter ((/=) x . fst) ys
removes xs ys = filter (flip notElem xs . fst) ys

fst3 (a,_,_) = a
