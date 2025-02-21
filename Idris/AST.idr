module AST

import Idris.Syntax
import Idris.Parser

import Core.FC
import Core.Name

import System
import System.File

import ErrOr

import Deriving.Show
%language ElabReflection

%default covering

-------------------------------------------------------------------------------

mapM : Monad m => (f : a -> m b) -> List a -> m (List b)
mapM f [] = pure []
mapM f (x :: xs) = do
  xs' <- mapM f xs
  x' <- f x
  pure (x' :: xs')

traverseWithSt : Monad m
              => {st : Type}
              -> (f : st -> a -> m (b, st))
              -> st
              -> List a
              -> m (List b, st)
traverseWithSt f st [] = pure ([], st)
traverseWithSt f st (x :: xs) = do
  (x', st') <- f st x
  (xs', st'') <- traverseWithSt f st' xs
  pure (x' :: xs', st'')

-------------------------------------------------------------------------------
-- Erlang IR

public export
data EPat : Type where
  EPVar : String -> EPat
  EPCst : String -> EPat
  EPBracket : List EPat -> EPat
  EPInfixApp : List EPat -> String -> List EPat -> EPat 
  EPPair : List EPat -> List EPat -> EPat 
  EPUnit : EPat 
  EPList : List EPat -> EPat

data EStmt : Type where
  ESVar   : String -> EStmt
  ESCst  : String -> EStmt -- numbers, strings, &c. NOT SURE ABOUT THIS
  ESApp   : String -> List EStmt -> EStmt
  ESInfixApp : EStmt -> String -> EStmt -> EStmt
  ESString : String -> EStmt
  ESMatchOp : List EPat -> EStmt -> EStmt
  ESMatchVar : String -> EStmt -> EStmt
  ESMacMod : EStmt
  ESList : List EStmt -> EStmt
  ESSelf : EStmt
  ESRecv : List (EPat, List EStmt) -> EStmt
  ESSend : EStmt -> EStmt -> EStmt
  EBracket : EStmt -> EStmt
  ESeq : EStmt -> EStmt -> EStmt
  ELam : List EPat -> EStmt -> EStmt
  EList : List EStmt -> EStmt
  EPair : List EStmt -> List EStmt -> EStmt
  EUnit : EStmt
  EComprehension : EStmt -> List EStmt -> EStmt
  ECase : EStmt -> List (List EPat, List EStmt) -> EStmt

data EDecl : Type where
  EDNil : EDecl
  EDFun : (dn : String) -> (cs : List (List EPat, List EStmt)) -> EDecl

data EMod : Type where
  EM : (mn : String) -> List EDecl -> EMod


%hint
showEPat : Show EPat 
showEPat = %runElab derive

%hint
showEStmt : Show EStmt 
showEStmt = %runElab derive

%hint
showEDecl : Show EDecl 
showEDecl = %runElab derive

%hint
showEMod : Show EMod 
showEMod = %runElab derive

-------------------------------------------------------------------------------
-- Pretty Print IR
mutual 

  eF : List EStmt -> String -> String 
  eF [] s = ""
  eF (s1::s2::ss) s = s 
  eF (s1::[]) s = s

  eP : List EPat -> String -> String 
  eP [] s = ""
  eP (s1::s2::ss) s = s 
  eP (s1::[]) s = s

  pFun : String -> String 
  pFun fun = 
    case fun of
      "filter" => "lists:filter"
      "sum" => "lists:sum"
      "map" => "lists:map"
      "length" => "length"
      "spawn" => "spawn"
      "Nat" => "nat"
      "MsgT" => "msgt"
      "fChan" => "utils:fst"
      "sChan" => "utils:snd"
      "chunk" => "utils:n_length_chunks"
      "fst" => "utils:fst2"
      "snd" => "utils:snd2"
      "zip1" => "lists:zip"
      "foldl" => "lists:foldl"
      "hd" => "hd"
      "tl" => "tl"
      "||" => "or"
      "==" => "=="
      "+" => "+"
      "*" => "*"
      "foldr" => "lists:foldr"
      "takeWhile" => "lists:takewhile"
      "minus" => "utils:minus"
      "not" => "not"
      "zipIt" => "lists:zip"
      "app" => "lists:append"
      "S" => "utils:s"
      "rem" => "rem"

      fn => "?MODULE:" ++ fn

  pVar : String -> String 
  pVar fun = 
    case fun of
      "Nat" => "nat"
      "MsgT" => "msgt"
      "True" => "true"
      "False" => "false"
      "andB" => "fun(X,Y) -> X and Y end"
      fn => fn

  pRecvs : Bool -> String -> String -> List (EPat, List EStmt) -> String 
  pRecvs b t e [] = ""
  pRecvs b t e ((p,cs) :: rest) = pPats " , " [p] ++ " -> " 
                        ++ pStmts b t e cs
                        ++ pRecvs b t e rest

  pStmts : Bool -> String -> String -> List EStmt -> String 
  pStmts b t e [] = "" 
  pStmts b t e (ESVar x :: ss) = t ++ (pVar x) ++ " " ++ (eF ss e) ++ pStmts b t e ss 
  pStmts b t e (ESCst c :: ss) = t ++ c ++ " " ++ (eF ss e) ++ pStmts b t e ss 
  pStmts b t e (ESApp fn args::ss) = 
    if fn == "Pure" || fn == "Return" then 
        t ++ pStmts b "" " , " args ++  (eF ss e) ++ pStmts b t e ss 

     else
        t ++ (pFun fn) ++ "( " ++ pStmts b "" " , " args ++ " ) " ++  (eF ss e) ++ pStmts b t e ss 
  pStmts b t e (ESInfixApp t1 str t2 :: ss) = 
    if str == "::" then 
      t 
      ++ "["
      ++ pStmts b "" e [t1]
      ++ " "
      ++ "|" 
      ++ " "
      ++ pStmts b "" e [t2]
      ++ "]"
      ++ (eF ss e)
      ++ pStmts b t e ss
       else if str == "++" then 
      t 
      ++ "lists:append("
      ++ pStmts b "" e [t1]
      ++ " "
      ++ "," 
      ++ " "
      ++ pStmts b "" e [t2]
      ++ ")"
      ++ (eF ss e)
      ++ pStmts b t e ss
       else 
         t 
      ++ pStmts b "" e [t1]
      ++ " "
      ++ (pFun str)
      ++ " "
      ++ pStmts b "" e [t2]
      ++ (eF ss e)
      ++ pStmts b t e ss
  pStmts b t e (ESString s::ss)  = t ++ "\"" ++ s ++ "\"" ++ (eF ss e) ++ pStmts b t e ss
  pStmts True t e (ESMatchOp pats st :: ss) = t 
                                          ++ pPats " , " pats
                                          ++ " <- "
                                          ++ pStmts True t e [st] 
                                          ++ (eF ss e) ++ pStmts True t e ss
  pStmts False t e (ESMatchOp pats st :: ss) = t 
                                          ++ pPats " , " pats
                                          ++ " = "
                                          ++ pStmts False t e [st] 
                                          ++ (eF ss e) ++ pStmts False t e ss
  pStmts True t e (ESMatchVar n rhs :: ss ) = t 
                                          ++ n
                                          ++ " <- "
                                          ++ pStmts True t e [rhs] 
                                          ++ (eF ss e) ++ pStmts True t e ss
  pStmts b t e (ESMatchVar n rhs :: ss ) = t 
                                          ++ n
                                          ++ " = "
                                          ++ pStmts b t e [rhs] 
                                          ++ (eF ss e) ++ pStmts b t e ss

  pStmts b t e (ESMacMod ::ss) = t ++ "?MODULE" ++ (eF ss e) ++ pStmts b t e ss 
  pStmts b t e (ESList sts :: ss) = t ++  "[ "
                               ++ pStmts b t " , " sts 
                               ++ " ] "
                               ++ (eF ss e) ++ pStmts b t e ss 
  pStmts b t e (ESSelf  :: ss) = t ++ "self() " ++ (eF ss e) ++ pStmts b t e ss 
  pStmts b t e (ESRecv cs :: ss) = t ++ "receive" ++ "\n\t\t"
                                 ++ pRecvs b (t++"\t") e cs
                             ++ (eF ss e) 
                             ++ "\n"
                             ++ t 
                             ++ "end"
                             ++ pStmts b t e ss 
  pStmts b t e (ESSend m s :: ss) = t ++ pStmts b "" "" [m] ++ " ! " ++ pStmts b "" "" [s] ++ (eF ss e) ++ pStmts b t e ss 
  pStmts b t e (EBracket ter :: ss) = t ++ " ( "
                                 ++ (pStmts b t e [ter])
                                 ++ " ) "
                                 ++ (eF ss e)
                                 ++ pStmts b t e ss 
  pStmts b t e (ESeq t1 t2 :: ss) =
           t ++ "lists:seq( "
        ++ (pStmts b t e [t1])
        ++ " , "
        ++ (pStmts b t e [t2])
        ++ " ) "
        ++ (eF ss e)
        ++ pStmts b t e ss  
  pStmts b t e (ELam p rhs :: ss) = 
         t ++ "fun ( "
      ++ pPats " , " p
      ++ " ) -> "
      ++ pStmts b t e [rhs] 
      ++ " end "
      ++ (eF ss e)
      ++ pStmts b t e ss 
  pStmts b t e (EList ts :: ss) = 
            t ++ "["
         ++ pStmts b "" "," ts
         ++ "]"
         ++ (eF ss e) 
         ++ pStmts b t e ss 
  pStmts b t e (EPair t1 t2 :: ss) = 
         t ++ "{"
         ++ pStmts b "" e t1
         ++ ","
         ++ pStmts b "" e t2
       --   ++ pStmts b "" "," ss 
         ++ "}"
         ++ (eF ss e) 
         ++ pStmts b t e ss 
  pStmts b t e (EUnit :: ss) =
    "{}"
    ++ (eF ss e)
    ++ pStmts b t e ss
  pStmts b t e (EComprehension term gens :: ss) = 
    "["
    ++ pStmts b "" "" [term]
    ++ " || "
    ++ pStmts True "" "," gens
    ++ "]"
    ++ (eF ss e)
    ++ pStmts b t e ss 
  pStmts b t e (ECase term clauses :: ss) = 
    "case "
    ++ pStmts b "" "" [term] 
    ++ "of\n"
    ++ pClauses "\t" clauses
    ++ "end"
    ++ (eF ss e)
    ++ pStmts b t e ss  


  pPats : String -> List EPat -> String 
  pPats e [] = ""
  -- pPats e (EPVar n::EPVar n2::pats) = n ++ " , " ++ n2 ++ pPats pats
  pPats e (EPVar n :: pats) = n ++ (eP pats e) ++ pPats e pats  
  pPats e (EPCst c :: pats) = c ++ (eP pats e) ++ pPats e pats 
  pPats e (EPBracket p :: pats) = "(" ++ (pPats e p) ++ ")" ++ (eP pats e) ++ pPats e pats
  pPats e (EPInfixApp p1 str p2 :: pats) = 
     if str == "::" then 
      "["
      ++ (pPats e p1)
      ++ "|"
      ++ (pPats e p2)
      ++ "]"
      ++ (eP pats e)
      ++ pPats e pats
     else 
      (pPats e p1)
      ++ str
      ++ (pPats e p2)
  pPats e (EPPair t1 t2 :: pats) = 
    "{"
    ++ (pPats e t1)
    ++ ","
    ++ (pPats e t2)
    ++ "}"
    ++ (eP pats e)
    ++ pPats e pats
  pPats e (EPUnit :: pats) =
    "{}"
    ++ (eP pats e)
    ++ pPats e pats
  pPats e (EPList [] :: pats) = 
    "[]"
    ++ (eP pats e)
    ++ pPats e pats
  pPats e (EPList xs :: pats) = "pPats not implemented"

  pClauses : String -> List (List EPat, List EStmt) -> String 
  pClauses n [] = ""
  pClauses n ((pats, stmts)::[]) =  n ++ " ( "
                                 ++ pPats " , " pats
                                 ++ " ) "
                                 ++ " -> \n"
                                 ++ pStmts False "\t" ",\n" stmts
                                 ++ "\n"
                                 
  pClauses n ((pats, stmts)::cs) =  n ++ " ( "
                                 ++ pPats " , " pats
                                 ++ " ) "
                                 ++ " -> \n"
                                 ++ pStmts False "\t" ",\n" stmts
                                 ++ ";\n"
                                 ++ pClauses n cs

  pDecs : List EDecl -> String 
  pDecs [] = ""
  pDecs (EDNil :: decs) = pDecs decs 
  pDecs (EDFun n cs :: decs) =  pClauses n cs ++ ".\n" ++ pDecs decs

  pMod : EMod -> String 
  pMod (EM name decs) =  "-module(" ++ name ++ ")." ++ "\n"
                      ++ "-compile(export_all).\n"
                      ++ pDecs decs 

-------------------------------------------------------------------------------
-- IR Generation -- Names

Env : Type
Env = List (String, String)

prelude : String -> EStmt
prelude "printLn"  = ESVar "io:format" -- N.B. newlines not preserved
prelude "putStrLn" = ESVar "io:format"
prelude "putStr"   = ESVar "io:format"
prelude "print"    = ESVar "io:format"
prelude "Halt"     = ESVar "halt"
prelude "MEnd"     = ESVar "mend"
prelude "Msg"      = ESVar "msg"
prelude str        = ESVar str

toEVarName : String -> String
toEVarName str =
  case strM str of
    StrNil => assert_total (idris_crash "toEVarName: impossible empty string")
    StrCons x xs => strCons (toUpper x) xs


lookup : Env -> String -> EStmt
lookup [] str = prelude str
lookup ((x,y) :: xs) str =
  if str == x then ESVar (toEVarName y) else lookup xs str

getNameStrFrmName : Env -> Name.Name -> ErrorOr String
getNameStrFrmName env n =
  case displayName n of
      (Nothing, n') => case lookup env n' of
        ESVar n'' => Just n''
        n'' => error
             $ "getNameStrFrmName: var lookup unexpected expand -- " ++ show n''
      _ => error "getNameStrFrmName -- non-empty namespace"

getNameStmtFrmName : Env -> Name.Name -> ErrorOr EStmt
getNameStmtFrmName env n =
  case displayName n of
      (Nothing, n') => Just (lookup env n')
      _ => error "getNameStmtFrmName -- non-empty namespace"

getNameFrmTerm : Env -> PTerm -> ErrorOr EStmt
getNameFrmTerm env (PRef fc' n) =
  getNameStmtFrmName env n
getNameFrmTerm env (PApp fc' f x) =
  getNameFrmTerm env f
getNameFrmTerm env tm =
  error $ "getNameFrmTerm -- unimplemented -- " ++ show tm

getNameFrmClause : Env -> PClause -> ErrorOr String
getNameFrmClause env (MkPatClause fc lhs _ _) = do
  ESVar n <- getNameFrmTerm env lhs
    | n =>
      error $ "getNameFrmClause: name causes unexpected expansion -- " ++ show n
  pure n
getNameFrmClause env (MkWithClause fc lhs _ _ _) =
  error "getNameFrmClause -- MkWithClause"
getNameFrmClause env (MkImpossible fc lhs) =
  error "getNameFrmClause -- MkImpossible"

-------------------------------------------------------------------------------
-- IR Generation -- Patterns

genEPats : Env -> PTerm -> ErrorOr (List EPat, Env)
genEPats env (PRef fc n) = do
  "Z" <- getNameStrFrmName env n
    | n' => case n' of 
              "MEnd" => pure ([EPVar "mend"], ("MEnd","mend") :: env)
              n'' => pure ([EPVar (toEVarName n'')], (n'',n'') :: env)
  pure ([EPVar "0"], ("Z","0") :: env)
genEPats env (PApp fc (PRef _ nm) (PRef _ nm2)) = do 
  "S" <- getNameStrFrmName env nm 
    | n => do  
              -- nm1 <- getNameStrFrmName env nm
              "Z" <- getNameStrFrmName env nm2 
                | nm2 => pure ([EPVar ((toEVarName nm2))], (nm2,nm2) :: env)
              pure ([EPVar "0"], ("Z","0") :: env)


  nm2' <- getNameStrFrmName env nm2 
               --env' <- rewriteN nm2' (nm2++"-1")
  pure ([EPVar (toEVarName nm2')], (nm2',(nm2'++"-1")) :: env)
genEPats env (PApp fc (PRef _ nm) x) = -- do 
 -- "S" <- getNameStrFrmName env nm 
 --   | n => do  (x', env' ) <- genEPats env x
 --              pure (((EPVar (toEVarName "S")) :: x'), env')
  genEPats env x 
genEPats env (PApp fc f x) = do
  (xs, env')  <- genEPats env f
  (ys, env'') <- genEPats env' x
  pure (xs ++ ys, env'')
genEPats env (PPair fc l r) = do
  (xs, env') <- genEPats env l
  (ys, env'') <- genEPats env' r
  pure ([EPPair xs ys], env'')
genEPats env (PPrimVal fc c) = do
    pure ([EPCst (show c)], env)
genEPats env (PBracketed fc t) = do 
  (t', env') <- genEPats env t 
  pure ([EPBracket t'], env')
genEPats env (POp f opFC str t1 t2) = do
    (t1', env') <- genEPats env t1
    (t2', env'') <- genEPats env' t2 
    pure ([EPInfixApp t1' (show str) t2'], env'')
genEPats env (PDPair fu op t1 t2 t3) = do
      (t1, env') <- genEPats env t1 
      (t2, env'') <- genEPats env' t3 
      pure ([EPPair t1 t2], env'')
genEPats env (PUnit _) =
  pure ([EPUnit], env)
genEPats env (PList _ _ []) = 
  pure ([EPList []], env)

genEPats env p = error $ "genEPats: unimplemented -- " ++ show p

genEPatsTop : Env -> PTerm -> ErrorOr (List EPat, Env)
genEPatsTop env (PRef fc n) = do
  "mend" <- getNameStrFrmName env n
    | n' => pure ([], env)
  pure ([EPVar "mend"], ("mend","mend") :: env) -- no arguments
genEPatsTop env (PApp fc (PRef _ nm) (PRef _ nm2)) = do 
  "msg" <- getNameStrFrmName env nm 
    | n => do  
              nm2' <- getNameStrFrmName env nm2
              pure ([EPVar (toEVarName nm2')], (nm2', nm2') :: env)
  nm2 <- getNameStrFrmName env nm2 
  pure ([EPPair [EPVar "msg"] [EPVar (toEVarName nm2)] ], (nm2,nm2) :: env)
            -- pure ([EPVar "0"], ("Z","0") :: env)
genEPatsTop env p = genEPats env p

-------------------------------------------------------------------------------
-- IR Generation -- Terms/Expressions/Statements

mutual
  genEStmtsDo : Env
             -> List PDo
             -> ErrorOr (List EStmt, Env)
  genEStmtsDo env [] = pure ([], env)
  genEStmtsDo env ((DoExp fc tm) :: dss) = do
    (es, env') <- genSend env tm
    (rest, env'') <- genEStmtsDo env' dss
    pure (es ++ rest, env'')
  genEStmtsDo env ((DoBindPat fc lhs rhs []) :: dss) = do
    ([x,y], env') <- genEPats env lhs
      | (xs, env') => do
        (e, env'') <- genEStmt env' rhs
        (rest, env''') <- genEStmtsDo env'' dss
        pure (ESMatchOp xs e :: rest, env''')
    (e@(ESApp "spawn" _), env'') <- genSpawn env' rhs -- SPAWN
      | (e, env'') => do
        (rest, env''') <- genEStmtsDo env'' dss
        pure (ESMatchOp [x,y] e :: rest, env''')
    (rest, env''') <- genEStmtsDo env'' dss
    pure (ESMatchOp [x] e :: rest, env''')
  genEStmtsDo env (DoBind fc nfc x rhs@(PApp _ (PRef _ fn) (PRef _ ch)) :: dss) = do
    x' <- getNameStrFrmName env x
    case displayName fn of
      (Nothing, "Recv") => do
        (rest, env') <- genEStmtsDo ((x',x') :: env) dss
        pure ([ESRecv [(EPVar (toEVarName x'), rest)]], env')
      _ => do
        (rhs', env') <- genEStmt ((x',x') :: env) rhs
        (rest, env'') <- genEStmtsDo env' dss
        pure (rhs' :: rest, env'')    
  genEStmtsDo env (DoBind fc nfc x rhs@(PApp _ (PApp _ (PRef _ fn) (PRef x2 ty)) ch) :: dss) = do
    x' <- getNameStrFrmName env x
    case displayName fn of
      (Nothing, "Recv") => do
        (rest, env') <- genEStmtsDo ((x',x') :: env) dss
        pure ([ESRecv [(EPVar (toEVarName x'), rest)]], env')
      _ => do
        (rhs', env') <- genEStmt env rhs 
        (rest, env'') <- genEStmtsDo ((x',x') :: env') dss
        pure (ESMatchVar (toEVarName x') rhs' :: rest, env'') 
  genEStmtsDo env (DoBind fc nfc x rhs :: dss) = do
    x' <- getNameStrFrmName env x
    (e@(ESApp "spawn" _), env') <- genSpawn env rhs -- SPAWN
       | (rhs', env') => do -- <- genEStmt ((x',x')::env) rhs
             (rest, env'') <- genEStmtsDo ((x',x') :: env') dss
             pure (ESMatchVar (toEVarName x') rhs' :: rest, env'')
    (rest, env'') <- genEStmtsDo ((x',x') :: env') dss
    pure (ESMatchVar (toEVarName x') e :: rest, env'')
   {- (e@(ESApp "spawn" _), env'') <- genSpawn env' rhs -- SPAWN
      | (e, env'') => do
        (rest, env''') <- genEStmtsDo env'' dss
        pure (ESMatchOp [x,y] e :: rest, env''')
    (rest, env''') <- genEStmtsDo env'' dss
    pure (ESMatchOp [x] e :: rest, env''')
    -}
    -- error $ "genEStmtsDo: unimplemented -- DoBind"
  genEStmtsDo env (DoBindPat _ _ _ _ :: dss) =
    error $ "genEStmtsDo: unimplemented -- DoBindPat"
  genEStmtsDo env (DoLet _ _ _ _ _ _ :: dss) =
    error $ "genEStmtsDo: unimplemented -- DoLet"
  genEStmtsDo env (DoLetPat _ _ _ _ _ :: dss) =
    error $ "genEStmtsDo: unimplemented -- DoLetPat"
  genEStmtsDo env (DoLetLocal _ _ :: dss) =
    error $ "genEStmtsDo: unimplemented -- DoLetLocal"
  genEStmtsDo env (DoRewrite _ _ :: ds) =
    error $ "genEStmtsDo: unimplemented -- DoRewrite"

  genEStmtsStr : PStr -> ErrorOr String
  genEStmtsStr (StrLiteral fc str) = Just str
  genEStmtsStr (StrInterp fc tm) =
    error $ "genEStmtsStr: unimplemented -- StrInterp"

  genEStmts : Env -> PTerm -> ErrorOr (List EStmt, Env)
  genEStmts env (PRef fc n) = do
    stmt <- getNameStmtFrmName env n
    pure ([stmt], env)
  genEStmts env (PApp fc f x) = do
    (ESApp fn xs, env')  <- genEStmt env f
      | (ESVar fn, env') => do
        (x', env'') <- genEStmt env' x
        case fn of 
          "msg" => do pure ([EPair [ESVar "msg"] [x']], env')
          _ => do pure ([ESApp fn [x']], env'')
      | f' => error $ "TODO: " ++ show f'
    (x', env') <- genEStmt env x
    pure ([ESApp fn (xs ++ [x'])], env')
  genEStmts env (PString fc ht strs) = do
    strs' <- mapM genEStmtsStr strs
    pure ([ESString (concat strs')], env)
  genEStmts env (PDoBlock fc mns dss) =
    genEStmtsDo env dss
  genEStmts env (PPrimVal fc c) = do
    pure ([ESCst (show c)], env)

  genEStmts env (PPair fc t1 t2) = do
    (t1, env') <- genEStmts env t1 
    (t2, env'') <- genEStmts env' t2
    pure ([EPair t1 t2], env'')

  genEStmts env (PBracketed fc t1) = do 
    (t1', env') <- genEStmt env t1 
    pure ([EBracket t1'], env')
  genEStmts env (PNamedApp fc p1 name p2) = error $ "genEStmts: PNamedApp unimplemented -- "  ++ show name
  genEStmts env (POp f opFC str t1 t2) = do
    (t1', env') <- genEStmt env t1 
    (t2', env'') <- genEStmt env' t2 
    pure ([ESInfixApp t1' (show str) t2'], env'')
  genEStmts env (PRange fc t1 mt2 t3) = do
     (t1', env') <- genEStmt env t1 
     (t3', env'') <- genEStmt env' t3
     pure ([ESeq t1' t3'], env'') 
  genEStmts env (PLam fc r pinf pat args scope) = do
     (pat', env') <- genEPats env pat 
     (rhs, env'') <- genEStmt env' scope 
     pure ([ELam pat' rhs], env'') 
  genEStmts env (PList fu ni li) = do 
    ts <- mapM (\x => genEStmt env x) (map snd li)
    pure ([EList (map fst ts)], env)
  genEStmts env (PDPair fu op t1 t2 t3) = do
      (t1, env') <- genEStmts env t1 
      (t2, env'') <- genEStmts env' t3 
      pure ([EPair t1 t2], env'')
  genEStmts env (PUnit _) =
    pure ([EUnit], env)
  genEStmts env (PComprehension fc t gens) = do
      (gens', env') <- genEStmtsDo env gens 
      (t', env'') <- genEStmt env' t 
      pure ([EComprehension t' gens'], env'')
  genEStmts env (PCase fc opts t cls) = do
      (t1, env') <- genEStmt env t 
      cls <- mapM (genEClause env') cls
      pure ([ECase t1 (trim cls)], env')



  genEStmts env tm = error $ "genEStmts: unimplemented -- "  ++ show tm

  genEStmt : Env -> PTerm -> ErrorOr (EStmt, Env)
  genEStmt env tm = do
    ((stmt :: _), env') <- genEStmts env tm
      | ([], _) => error $ "genEStmt: no statements generated"
    pure (stmt, env')

  genSpawn : Env -> PTerm -> ErrorOr (EStmt, Env)
  genSpawn env tm@(PApp _ (PApp _ (PApp _ (PRef _ fn) (PRef _ ty1)) (PRef _ ty2)) (PRef _ p)) =
    case displayName fn of
      (Nothing, "Spawn") => do
        pStr <- getNameStmtFrmName env p
        Just (ESApp "spawn" [ESMacMod, pStr, ESList [ESVar "chan", ESSelf]], env)
      (Nothing, "rem") => error $ "rem!!"
      _ => genEStmt env tm
  genSpawn env tm = genEStmt env tm

  genSend : Env -> PTerm -> ErrorOr (List EStmt, Env)
  -- genSend env tm@(PApp _ (PApp _ (PRef _ fn) (PRef _ ch)) msg) = 
  genSend env tm@(PApp _ (PApp _ (PRef _ fn) t) msg) = 
    do
    "Send" <- getNameStrFrmName env fn
      | fn' => genEStmts env tm
    -- ch' <- getNameStrFrmName env ch
    (ch', env') <- genEStmt env t
    (msg', env'') <- genEStmt env' msg
    pure ([ESSend ch' msg'], env'')
  genSend env tm = genEStmts env tm


-------------------------------------------------------------------------------
-- IR Generation -- Clauses/Statements

  genEClause : Env -> PClause -> ErrorOr (List EPat, List EStmt, Env)
  genEClause env (MkPatClause fc lhs rhs []) = do
    (pats, env') <- genEPatsTop env lhs
    (stmts, env'') <- genEStmts env' rhs
    Just (pats, stmts, env'')
  genEClause e c = error $ "genEClause: unimplemented -- " ++ show c

-------------------------------------------------------------------------------
-- IR Generation -- Declarations
  trim :  List (List EPat, (List EStmt, Env)) ->  List (List EPat, List EStmt)
  trim [] = []
  trim ((pats, (stmts, env)) :: rest) = (pats, stmts) :: trim rest


genEDecl : PDecl -> ErrorOr EDecl
genEDecl (PDef fc cs@(c :: _)) = do
  dn <- getNameFrmClause [] c
  body <- mapM (genEClause []) cs
  pure (EDFun dn (trim body)) -- FIXME -- Parameters
-- 
genEDecl (PClaim fc rc v fopts ty) =
  Just EDNil -- we don't care for type signatures
genEDecl (PData fc doc wd m p) = 
  Just EDNil -- we don't care for data types
genEDecl d = error $ "genEDecl: unimplemented -- " ++ show d

-------------------------------------------------------------------------------
-- IR Generation -- Modules

genIR : Module -> ErrorOr EMod
genIR m = do
  ds <- mapM genEDecl m.decls
  Just (EM "example" ds)


-----------------------------------------------------------------------------

main : String -> String -> IO ()
main i o = do
  let fName = i

  let srcLoc = PhysicalIdrSrc (mkModuleIdent Nothing o)

  Right rawSrc <- readFile fName
    | Left err => printLn err
  let Right (ws, st, mod) = runParser srcLoc Nothing rawSrc (prog srcLoc)
    | Left err => printLn err

  traverse_ printLn $ mod.decls
  -- traverse_ genPDecl mod.decls
  let Just ir = genIR mod
    | Err (StdErr err) => die err
    
  -- putStrLn (showEMod mod)
  putStrLn (show ir)

  putStrLn (pMod ir)