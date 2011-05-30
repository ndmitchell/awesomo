{-# LANGUAGE DeriveDataTypeable, PatternGuards #-}

module Core(
    Var, Con, Exp(..), Pat,
    pretty, parseFile
    ) where


import Data.Maybe
import Data.List
import Data.Data
import Control.Monad.State
import Data.Char
import Language.Haskell.Exts hiding (Exp,Name,Pat,Var,Let,App,Case,Con,name,parseFile)
import qualified Language.Haskell.Exts as H
import Data.Generics.Uniplate.Data
import qualified Data.Map as Map


parseFile :: FilePath -> IO Exp
parseFile = fmap (flip Let "main" . fromHSE . fromParseResult) . H.parseFile


---------------------------------------------------------------------
-- TYPE

type Var = String
type Con = String


data Exp = Con  Con [Var]
         | App  Var [Var]
         | Lam  Var Exp
         | Case Var [(Pat,Exp)]
         | Let  [(Var,Exp)] Var
           deriving (Data,Typeable,Show,Eq)

pretty :: Exp -> String
pretty = prettyPrint . toExp


type Pat = Exp


type Env = Var -> Maybe Exp

arity :: Var -> Maybe Int
arity x | '\'':xs <- dropWhile (/= '\'') x = Just $ read xs
        | otherwise = Nothing


env :: [(Var,Exp)] -> Env
env xs = flip Map.lookup mp
    where mp = Map.fromList xs


vars :: Exp -> [Var]
vars (Con _ xs) = xs
vars (App x xs) = x:xs
vars (Lam x y) = x : vars y
vars (Case x y) = x : concat [vars a ++ vars b | (a,b) <- y]
vars (Let x y) = concat [a : vars b | (a,b) <- x] ++ [y]


free :: Exp -> [Var]
free (Con _ xs) = nub xs
free (App x xs) = nub $ x:xs
free (Lam x y) = delete x $ free y
free (Case x y) = nub $ x : concat [free b \\ vars a | (a,b) <- y]
free (Let x y) = nub (concatMap (free . snd) x ++ [y]) \\ map fst x


subst :: [(Var,Var)] -> Exp -> Exp
subst [] x = x
subst ren e = case e of
    Con c vs -> Con c $ map f vs
    App x ys -> App (f x) (map f ys)
    Lam x y -> Lam x (g [x] y)
    Case x y -> Case (f x) [(a, g (vars a) b) | (a,b) <- y]
    Let x y -> Let [(a,g (map fst x) b) | (a,b) <- x] $ if y `elem` map fst x then y else f y
    where
        f x = fromMaybe x $ lookup x ren
        g del x = subst (filter (flip notElem del . fst) ren) x


valid :: Exp -> Bool
valid = all (isJust . arity) . free

validId :: Exp -> Exp
validId x | valid x = x
          | otherwise = error $ "Invalid expression:\n" ++ pretty x


---------------------------------------------------------------------
-- FLAT TYPE

data FlatExp = FlatExp [Var] [(Var,Exp)] Var

toFlat :: Exp -> FlatExp
toFlat = f []
    where
        f vs (Lam v x) = f (vs++[v]) x
        f vs (Let xs y) = FlatExp vs xs y
        f vs x = FlatExp vs [("_flat",x)] "_flat"


fromFlat :: FlatExp -> Exp
fromFlat (FlatExp vs x y) = lams vs $ Let x y

lams [] x = x
lams (l:ls) x = Lam l $ lams ls x


---------------------------------------------------------------------
-- FROM HSE

fromHSE :: Module -> [(Var,Exp)]
fromHSE (Module _ _ _ _ _ _ xs) = concatMap fromDecl xs


fromDecl :: Decl -> [(Var,Exp)]
fromDecl (PatBind _ (PVar f) Nothing (UnGuardedRhs x) (BDecls [])) = [(fromName f, fromExp x)]
fromDecl (FunBind [Match _ f vars Nothing (UnGuardedRhs x) (BDecls [])]) = [(fromName f, fromExp $ Lambda sl vars x)]
fromDecl TypeSig{} = []
fromDecl DataDecl{} = []
fromDecl TypeDecl{} = []
fromDecl x = error $ "Unhandled fromDecl: " ++ show x


fromExp :: H.Exp -> Exp
fromExp (Lambda _ [] x) = fromExp x
fromExp (Lambda _ (PVar (Ident x):vars) bod) = Lam x $ fromExp $ Lambda sl vars bod
fromExp o@(H.App x y) = Let [(f1,fromExp x),(f2,fromExp y),(f3,App f1 [f2])] f3
    where f1:f2:f3:_ = freshNames o
fromExp (H.Var (UnQual x)) = App (fromName x) []
fromExp (H.Con (UnQual x)) = Con (fromName x) []
fromExp (H.Con (Special Cons)) = Con ":" []
fromExp (LeftSection x (QVarOp y)) = fromExp $ H.App (H.Var y) x
fromExp (Paren x) = fromExp x
fromExp o@(H.Case x xs) = Let [(f1,fromExp x),(f2,Case f1 $ map fromAlt xs)] f2
    where f1:f2:_ = freshNames o
fromExp (List []) = Con "[]" []
fromExp (List [x]) = fromExp $ InfixApp x (QConOp (Special Cons)) $ List []
fromExp o@(InfixApp x (QConOp (Special Cons)) y) = Let [(f1,fromExp x),(f2,fromExp y),(f3,Con ":" [f1,f2])] f3
    where f1:f2:f3:_ = freshNames o
fromExp o@(InfixApp a (QVarOp b) c) = fromExp $ H.App (H.App (H.Var b) a) c
fromExp (Lit x) = Con (prettyPrint x) []
fromExp x@(NegApp _) = Con (prettyPrint x) []
fromExp (If a b c) = fromExp $ H.Case a [f "True" b, f "False" c]
    where f con x = Alt sl (PApp (UnQual $ Ident con) []) (UnGuardedAlt x) (BDecls [])
fromExp o@(H.Let (BDecls xs) x) = Let ((f1,fromExp x):concatMap fromDecl xs) f1
    where f1:_ = freshNames o
fromExp o@(Tuple xs) = Let
    ((f1, Con (fromTuple xs) (take (length xs) fs)) : zipWith (\f x -> (f,fromExp x)) fs xs) f1
    where f1:fs = freshNames o
fromExp (H.Con (Special (TupleCon _ n))) = Con (fromTuple $ replicate n ()) []
fromExp x = error $ "Unhandled fromExp: " ++ show x


fromName :: H.Name -> String
fromName (Ident x) = x
fromName (Symbol x) = x

fromAlt :: Alt -> (Pat, Exp)
fromAlt (Alt _ pat (UnGuardedAlt bod) (BDecls [])) = (fromPat pat, fromExp bod)
fromAlt x = error $ "Unhandled fromAlt: " ++ show x

fromPat :: H.Pat -> Pat
fromPat (PParen x) = fromPat x
fromPat (PList []) = Con "[]" []
fromPat (PApp (Special Cons) xs) = Con ":" $ map fromPatVar xs
fromPat (PInfixApp a b c) = fromPat $ PApp b [a,c]
fromPat (PApp (UnQual c) xs) = Con (fromName c) $ map fromPatVar xs
fromPat (PTuple xs) = Con (fromTuple xs) $ map fromPatVar xs
fromPat (PApp (Special (TupleCon _ n)) xs) = Con (fromTuple xs) $ map fromPatVar xs
fromPat PWildCard = App "_wild" []
fromPat x = error $ "Unhandled fromPat: " ++ show x

fromTuple xs = "(" ++ replicate (length xs - 1) ',' ++ ")"

fromPatVar :: H.Pat -> String
fromPatVar (PVar x) = fromName x
fromPatVar x = error $ "Unhandled fromPatVar: " ++ show x


freshNames :: H.Exp -> [String]
freshNames x  = ['v':show i | i <- [1..]] \\ [y | Ident y <- universeBi x]


---------------------------------------------------------------------
-- TO HSE

toHSE :: [(Var,Exp)] -> Module
toHSE xs = Module sl (ModuleName "") [] Nothing Nothing [] $ map toDecl xs

toDecl :: (Var,Exp) -> Decl
toDecl (f,x) = PatBind sl (PVar $ Ident f) Nothing (UnGuardedRhs $ toExp x) (BDecls [])

toExp :: Exp -> H.Exp
toExp (Lam x y) = Paren $ lambda [PVar $ Ident x] $ toExp y
toExp (Let xs y) = Paren $ H.Let (BDecls $ map toDecl xs) $ toVar y
toExp (App x y) = Paren $ foldl H.App (toVar x) $ map toVar y
toExp (Case x y) = Paren $ H.Case (toVar x) (map toAlt y)
toExp (Con c vs) = Paren $ foldl H.App (H.Con $ UnQual $ toName c) (map toVar vs)

toAlt :: (Pat, Exp) -> Alt
toAlt (x,y) = Alt sl (toPat x) (UnGuardedAlt $ toExp y) (BDecls [])

toPat :: Pat -> H.Pat
toPat (Con c vs) = PApp (UnQual $ toName c) (map (PVar . Ident) vs)
toPat (App v []) = PWildCard
toPat x = error $ "toPat, todo: " ++ show x

toVar :: Var -> H.Exp
toVar x = H.Var $ UnQual $ toName x

toName :: String -> H.Name
toName xs@(x:_) | isAlphaNum x || x `elem` "'_(" = Ident xs
                | otherwise = Symbol xs

sl = SrcLoc "" 0 0


lambda v1 (Lambda _ v2 x) = Lambda sl (v1++v2) x
lambda v1 (Paren x) = lambda v1 x
lambda v1 x = Lambda sl v1 x
