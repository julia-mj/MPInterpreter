-- Wymagamy, by moduł zawierał tylko bezpieczne funkcje
{-# LANGUAGE Safe #-}
-- Definiujemy moduł zawierający rozwiązanie.
-- Należy zmienić nazwę modułu na {Imie}{Nazwisko} gdzie za {Imie}
-- i {Nazwisko} należy podstawić odpowiednio swoje imię i nazwisko
-- zaczynające się wielką literą oraz bez znaków diakrytycznych.
module JuliaMajkowska (typecheck, eval) where

-- Importujemy moduły z definicją języka oraz typami potrzebnymi w zadaniu
import AST
import DataTypes


import Data.Map (Map)
import qualified Data.Map as Map

-- Typowanie
data Error p = Error p String

data Environment t = Environment (Map Var t) 

types_bin :: Expr p -> (Type , Type)
types_bin (EBinary p BAnd _ _ ) = (TBool, TBool)
types_bin (EBinary p BOr _ _ ) = (TBool, TBool)
types_bin (EBinary p BEq _ _ ) = (TInt, TBool)
types_bin (EBinary p BNeq _ _ ) = (TInt, TBool)
types_bin (EBinary p BLt _ _ ) = (TInt, TBool)
types_bin (EBinary p BGt _ _ ) = (TInt, TBool)
types_bin (EBinary p BLe _ _ ) = (TInt, TBool)
types_bin (EBinary p BGe _ _ ) = (TInt, TBool)
types_bin (EBinary p BAdd _ _ ) = (TInt, TInt)
types_bin (EBinary p BSub _ _ ) = (TInt, TInt)
types_bin (EBinary p BMul _ _ ) = (TInt, TInt)
types_bin (EBinary p BDiv _ _ ) = (TInt, TInt)
types_bin (EBinary p BMod _ _ ) = (TInt, TInt)

types_pair ::Type -> p -> String -> Either (Error p) Type
types_pair (TPair x _) _ "fst"= Right x
types_pair (TPair _ x) _ "snd"= Right x
types_pair t p s = Left (JuliaMajkowska.Error (p) ("Brak zgodnosci typow - oczekiwano Pair odnaleziono " ++ (show t)))

update_env :: Environment Type -> Var-> Type -> Environment Type
update_env (Environment env) a typ = (Environment (Map.insert a typ env))

check_type :: Environment Type -> Expr p -> Type -> Either (Error p) Type
check_type env expr typ =
    let realtype = infer_type env expr
    in case realtype of
        Right typ1 -> if typ == typ1
                        then realtype
                        else Left (JuliaMajkowska.Error (getData expr) ("Brak zgodnosci typow - oczekiwano " ++ (show typ) ++ " odnaleziono " ++ (show typ1)))
        Left error -> Left error

infer_type :: Environment Type -> Expr p -> Either (Error p) Type

infer_type env (ENum _ _) = Right TInt
infer_type env (EBool _ _) = Right TBool
infer_type env (EUnit _) = Right TUnit
infer_type (Environment env) (EVar p x) =
    let typ = Map.lookup x env
    in case typ of
       Just val -> Right val
       Nothing -> Left (JuliaMajkowska.Error p "Zmienna niezainicjalizowana") -- Right TInt
infer_type env (EPair p x y) = do
    typ1 <- infer_type env x
    typ2 <- infer_type env y
    return (TPair typ1 typ2)

infer_type env (EFst p x) = do
    typ <- infer_type env x
    types_pair typ p "fst"
    
infer_type env (ESnd p x) = do
    typ <- infer_type env x
    types_pair typ p "snd" 
 
infer_type env (ENil p (TList a)) = Right (TList a)
infer_type env (ENil p t) = Left (JuliaMajkowska.Error (p) ("Brak zgodnosci typow - oczekiwano List Type odnaleziono " ++ (show t)))

infer_type env (ECons p x y) = do
    tx <- infer_type env x
    check_type env y (TList tx)

infer_type env (EMatchL p e ifempty (glowa, ogon, ifnotempty)) = 
    case infer_type env e of
        Left error -> Left error
        Right (TList t1) -> do 
                        tifemp <- infer_type env ifempty
                        check_type newenv ifnotempty tifemp
                        where newenv = update_env (update_env env glowa t1) ogon (TList t1)
        Right nielista -> Left (JuliaMajkowska.Error (p) ("Brak zgodnosci typow - oczekiwano List Type odnaleziono " ++ (show nielista)))                                    

infer_type env (EUnary  p UNeg expr) = check_type env expr TInt
infer_type env (EUnary  p UNot expr) = check_type env expr TBool

infer_type env (EBinary p op a b) = 
    let intype = fst (types_bin (EBinary p op a b)) 
        checka = check_type env a intype
        checkb = check_type env b intype
        outtype = snd (types_bin (EBinary p op a b))
    in case checka of 
            Left error -> Left error
            Right typ1 ->  case checkb of
                            Left error -> Left error
                            Right typ2 -> Right outtype

infer_type env (ELet p v a b )  = do
    typ  <- infer_type env a
    infer_type (update_env env v typ) b
        

infer_type env ( EIf p a b c) = 
    let checka = check_type env a TBool
        checkb = infer_type env b
    in case checka of
        Left error -> Left error
        Right typ -> case checkb of
                        Left error -> Left error
                        Right typ1 -> check_type env c typ1

infer_type env (EApp p e1 e2) = do 
    type1 <- infer_type env e1
    type2 <-infer_type env e2
    apply type1 type2 p

infer_type env (EFn p var typ wyrazenie) = 
    case infer_type (update_env env var typ) wyrazenie of
        Left error -> Left error
        Right typw -> Right (TArrow typ typw)


apply :: Type -> Type -> p -> Either (Error p) Type
apply (TArrow a b) c p = if a == c
                            then Right b
                            else Left (JuliaMajkowska.Error p ("Niezgodność typów w aplikacji funkcji - oczekiwano " ++ (show a) ++" odnaleziono " ++ (show b)))
apply x y p = Left (JuliaMajkowska.Error p ("Aplikacja do wyrażenia które nie jest funkcją"))    
    
konwertuj :: Either (Error p) Type -> Expr p -> TypeCheckResult p
konwertuj x expr = case x of
    Right typ -> if typ == TInt
                    then Ok
                    else DataTypes.Error (getData expr) ("Zły typ danych wyjściowych programu - oczekiwano Integer odnaleziono Boolean")
    Left (JuliaMajkowska.Error pos mes) -> (DataTypes.Error pos mes)

type_function:: Environment Type -> FunctionDef p -> Either (Error p) Type
type_function env (FunctionDef p name argname argtype restype body) = 
    check_type (update_env env argname argtype) body restype

check_functions:: [FunctionDef p] -> Environment Type -> Either (Error p) (Environment Type)
check_functions [] f = Right f
check_functions (x : xs) f = case type_function f x of
                                Left error -> Left error
                                Right _ -> check_functions xs f

make_functions :: [FunctionDef p] -> Environment Type
make_functions [] = Environment (Map.empty)
make_functions (x : xs) = 
    let (Environment a) = make_functions xs 
    in Environment (Map.insert (funcName x) (TArrow (funcArgType x) (funcResType x))a)

initialize_env :: Environment Type -> [Var]-> Environment Type
initialize_env env [] = env
initialize_env env (x : xs) = 
    let (Environment tail) = (initialize_env env xs)
    in Environment (Map.insert x TInt tail)

-- Czy można nadpisać funkcję zmienną na wejsciu?
-- Funkcja sprawdzająca typy
-- Dla wywołania typecheck fs vars e zakładamy, że zmienne występujące
-- w vars są już zdefiniowane i mają typ int, i oczekujemy by wyrażenia e
-- miało typ int
-- UWAGA: to nie jest jeszcze rozwiązanie; należy zmienić jej definicję.

typecheck :: [FunctionDef p] -> [Var] -> Expr p -> TypeCheckResult p
typecheck f lista expr= 
    let fun = make_functions f
        env = initialize_env fun lista
    in case check_functions f fun of
        Left (JuliaMajkowska.Error pos mes) -> (DataTypes.Error pos mes)
        Right _ ->  konwertuj (infer_type env expr) expr


-- Funkcja obliczająca wyrażenia
-- Dla wywołania eval fs input e przyjmujemy, że dla każdej pary (x, v)
-- znajdującej się w input, wartość zmiennej x wynosi v.
-- Możemy założyć, że definicje funckcji fs oraz wyrażenie e są dobrze
-- typowane, tzn. typecheck fs (map fst input) e = Ok
-- UWAGA: to nie jest jeszcze rozwiązanie; należy zmienić jej definicję.

{-
 test fun f(x : int): int = x - parsuje sie
input x in
let f = x in f f
 test fun f (x:int) : int = x + 1 input f in f f - nie parsuje sie bo nadpisanie f
 -}

data Values t = Values (Map Var t)
data Val = VInt Integer | VBool Bool | VUnit | VPair Val Val | VList [Val] | VFunc (Val -> (Either ValError Val))
data ValError = Wrong_data
data FuncEnv t = FuncEnv (Map Var ((FuncEnv t) -> t -> Either ValError t))

update_vals :: Values Val-> Var -> Val -> Values Val
update_vals (Values vals) v wartosc = Values (Map.insert v wartosc vals)


compute :: [Val] -> Expr p -> Either ValError Val
compute [VBool a] (EUnary p UNot x)  = Right (VBool (not a))
compute [VInt a] (EUnary p UNeg x)  = Right (VInt (-a))
compute [(VBool a), (VBool b)] (EBinary p BAnd x y) = Right (VBool (a && b))
compute [(VBool a), (VBool b)] (EBinary p BOr x y) = Right (VBool (a || b))
compute [(VInt a), (VInt b)] (EBinary p BEq x y) = Right (VBool (a == b))
compute [(VInt a), (VInt b)] (EBinary p BNeq x y) = Right (VBool (a /= b))
compute [(VInt a), (VInt b)] (EBinary p BLt x y) = Right (VBool (a < b))
compute [(VInt a), (VInt b)] (EBinary p BGt x y) = Right (VBool (a > b))
compute [(VInt a), (VInt b)] (EBinary p BLe x y) = Right (VBool (a <= b))
compute [(VInt a), (VInt b)] (EBinary p BGe x y) = Right (VBool (a >= b))
compute [(VInt a), (VInt b)] (EBinary p BAdd x y) = Right (VInt (a + b))
compute [(VInt a), (VInt b)] (EBinary p BSub x y) = Right (VInt (a - b))
compute [(VInt a), (VInt b)] (EBinary p BMul x y) = Right (VInt (a * b))
compute [(VInt a), (VInt b)] (EBinary p BDiv x y) = if b == 0
                                                    then Left Wrong_data
                                                    else Right (VInt (div a b))
compute [(VInt a), (VInt b)] (EBinary p BMod x y) = if b ==0
                                                    then Left Wrong_data
                                                    else Right (VInt (mod a b))



find_value :: Values Val -> Expr p -> Either ValError Val
find_value vals (ENum p x) = Right (VInt x)
find_value vals (EBool p x) = Right (VBool x)
find_value vals (EUnit p) = Right VUnit
find_value vals (EPair p x y) = do 
    vx <- find_value vals x
    vy <- find_value vals y
    return (VPair vx vy)
find_value vals (EFst p e) = 
    let ve = find_value vals e    
    in case ve of
        Left error -> Left error
        Right (VPair e1 e2) -> Right e1
find_value vals (ESnd p e) = 
    let ve = find_value vals e    
    in case ve of
        Left error -> Left error
        Right (VPair e1 e2) -> Right e2
find_value vals (ENil p _) = Right (VList [])

find_value vals (ECons p x y) = do
    vx <- find_value vals x
    case find_value vals y of
        Left error -> Left error
        Right (VList a) -> Right (VList (vx : a))

find_value vals (EMatchL p expr ifempty (glowa, ogon, ifnotempty)) = 
    case find_value vals expr of
        Left error -> Left error
        Right (VList lista) -> case lista of
                                [] -> find_value vals ifempty
                                (h : t) -> find_value (update_vals (update_vals vals glowa h) ogon (VList t)) ifnotempty
                               
find_value (Values vals) (EVar p x) = 
    case (Map.lookup x vals) of
        Just v -> Right v
        Nothing -> Left Wrong_data

find_value vals (EUnary p op x) = do
    wartosc <- find_value vals x
    compute [wartosc] (EUnary p op x)

find_value vals (EBinary p op x y) = do
    wartosc <- find_value vals x
    wartosc2 <- find_value vals y
    (compute [wartosc, wartosc2] (EBinary p op x y))

find_value vals (ELet p v x y) = do
    wartosc <- find_value vals x
    find_value (update_vals vals v wartosc) y

find_value vals  (EIf p x y z) = 
    case find_value vals x of
         Left Wrong_data -> Left Wrong_data
         Right (VBool x) -> case x of
                            True -> find_value vals y
                            False -> find_value vals z

find_value vals (EApp p e1 e2) =
    case find_value vals e1 of
        Left error -> Left error
        Right (VFunc funkcja) -> do 
                                wartosc <- find_value vals e2
                                funkcja wartosc

find_value vals (EFn p var _ e) = Right (VFunc (\a -> find_value (update_vals vals var a) e) )

convert_eval :: Either ValError Val -> EvalResult
convert_eval x = case x of
    Left Wrong_data -> RuntimeError
    Right (VInt x) -> DataTypes.Value x

init_values :: [(Var,Integer)] -> Values Val-> Values Val
init_values [] v = v
init_values ((a, b):xs) v = 
    let (Values tail) = (init_values xs v)
    in Values (Map.insert a (VInt b) tail)

init_funcs :: [FunctionDef p] -> Values Val
init_funcs l =
    (Values result)
    where
        (Values result) = internal l
        internal [] = Values Map.empty
        internal (x : xs) = 
            let (Values posrednie) = (internal xs)
                lamb  = (\arg -> find_value (Values (Map.insert (funcArg x) arg result )) (funcBody x))
            in Values (Map.insert (funcName x) (VFunc lamb)  posrednie)

eval :: [FunctionDef p] -> [(Var,Integer)] -> Expr p -> EvalResult
eval f v e = convert_eval (find_value (init_values v (init_funcs f))  e)
