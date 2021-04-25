module Main

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings
import public Specdris.Spec

data Term = TmVar String
          | TmAbs String Term
          | TmApp Term Term
          | TmError String

Show Term where
  show (TmVar var) = "(TmVar " ++ show var ++ ")"
  show (TmAbs var t) = "(TmAbs " ++ show var ++ ", " ++ show t ++ ")"
  show (TmApp t1 t2) = "(TmApp " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (TmError cause) = "(ERROR: " ++ cause ++ ")"


data TermDB = TmVarDB Int Int
            | TmAbsDB String TermDB
            | TmAppDB TermDB TermDB
            | TmErrorDB String

Eq TermDB where
  (TmVarDB i d) == (TmVarDB i2 d2) = i == i2 && d == d2
  (TmAbsDB n t) == (TmAbsDB n2 t2) = n == n2 && t == t2
  (TmAppDB t1 t2) == (TmAppDB t12 t22) = t1 == t12 && t2 == t22
  (TmErrorDB err) == (TmErrorDB err2) = err == err2
  _ == _ = False

Show TermDB where
  show (TmVarDB var depth) = "(TmVarDB " ++ show var ++ ", " ++ show depth ++ ")"
  show (TmAbsDB name t) = "(TmAbsDB " ++ name ++ ", " ++ show t ++ ")"
  show (TmAppDB t1 t2) = "(TmAppDB " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (TmErrorDB cause) = "(ERROR: " ++ cause ++ ")"

data Binding =
  NameBinding String

Context : Type
Context = List Binding

index : String -> Context -> Maybe Int
index name ctx = go 0 ctx where
  go : Int -> Context -> Maybe Int
  go level ((NameBinding name2)::bindings) = if name2 == name then Just level else go (level + 1) bindings
  go _ Nil = Nothing

total
toDB : Int -> Context -> Term -> TermDB
toDB depth ctx (TmVar name) =
  case index name ctx of
       Just index => TmVarDB index depth
       Nothing => TmErrorDB $ "unknown variable: " ++ name
toDB depth ctx (TmAbs name t) =
  let ctx' = (NameBinding name) :: ctx
      t' = toDB (depth + 1) ctx' t
   in TmAbsDB name t'
toDB depth ctx (TmApp t1 t2) = TmAppDB (toDB depth ctx t1) (toDB depth ctx t2)
toDB _ _ (TmError cause) = TmErrorDB $ "parser error: " ++ cause

identifierParser : Parser String
identifierParser = pack <$> (lexeme $ some alphaNum)

varParser : Parser Term
varParser = TmVar <$> identifierParser

mutual
  absParser : Parser Term
  absParser = do
    _ <- lexeme $ char '\\'
    var <- identifierParser
    _ <- lexeme $ char '.'
    t <- termParser
    pure $ TmAbs var t

  appParameterParser : Parser Term
  appParameterParser = (varParser <|>| parens termParser)

  appParser : Parser Term
  appParser = do
    params <- some appParameterParser
    pure $ case nonEmpty params of
                Yes _ => foldlAsFoldr TmApp (head params) (tail params)
                No _ => TmError "TmApp: not enough arguments"

  termParser : Parser Term
  termParser = absParser <|> appParser <|> varParser

total
shift : Int -> Int -> TermDB -> TermDB
shift level d (TmAbsDB name t) = TmAbsDB name (shift (level + 1) d t)
shift level d (TmVarDB i size) = if i >= level then TmVarDB (i + d) (size + d) else TmVarDB i (size + d)
shift level d (TmAppDB t1 t2) = TmAppDB (shift level d t1) (shift level d t2)
shift level d err@(TmErrorDB err) = err

total
subst : Int -> TermDB -> TermDB -> TermDB
subst index (TmAbsDB x t1) t2 = TmAbsDB x (subst (index + 1) t1 t2)
subst index (TmAppDB t11 t12) t2 = TmAppDB (subst index t11 t2) (subst index t12 t2)
subst index var@(TmVarDB i size) t2 = if (i == index) then (shift 0 index t2) else var
subst _ err@(TmErrorDB _) _ = err

total
substitute : TermDB -> TermDB -> TermDB
substitute to what = subst 0 to what

isVal : TermDB -> Bool
isVal (TmAbsDB _ _) = True
isVal _ = False

total
eval1 : TermDB -> Maybe TermDB
eval1 (TmAppDB (TmAbsDB _ t1) t2@(TmAbsDB _ _)) = Just $ shift 0 (-1) (substitute t1 (shift 0 1 t2))
eval1 (TmAppDB t1@(TmAbsDB name t) t2) =
  let maybet2' = (eval1 t2)
   in (\t2' => TmAppDB t1 t2') <$> maybet2'
eval1 (TmAppDB t1 t2) =
  let maybet1' = (eval1 t1)
   in (\t1' => TmAppDB t1' t2) <$> maybet1'
eval1 _ = Nothing

eval : TermDB -> TermDB
eval t = case eval1 t of
              Just t' => if (t == t') then t else eval t'
              Nothing => t

stepeval : List TermDB -> TermDB -> List TermDB
stepeval acc t = case eval1 t of
                      Just t' => if (t == t') then acc else stepeval (t::acc) t'
                      Nothing => t::acc

fullStep : String -> Either String (List TermDB)
fullStep str  = (stepeval Nil) <$> toDB 0 Nil <$> (Strings.parse termParser str)

full : String -> Either String TermDB
full str  = eval <$> toDB 0 Nil <$> (Strings.parse termParser str)

parse : String -> Either String TermDB
parse str  = toDB 0 Nil <$> (Strings.parse termParser str)

evalTest : IO ()
evalTest = spec $ do
  describe "shift" $ do
    it "shifts free variables" $ do
      shift 0 10 (TmVarDB 0 1) `shouldBe` TmVarDB 10 11
      shift 0 10 (TmVarDB 1 2) `shouldBe` TmVarDB 11 12
    it "does not shift bound variables only the depth" $ do
      shift 1 10 (TmVarDB 0 1) `shouldBe` TmVarDB 0 11
      shift 2 10 (TmVarDB 1 2) `shouldBe` TmVarDB 1 12
    it "increases the depth threshold in an abstraction" $ do
      shift 0 10 (TmAbsDB "x" $ TmVarDB 0 1) `shouldBe` (TmAbsDB "x" $ TmVarDB 0 11)
      shift 0 10 (TmAbsDB "x" $ TmVarDB 1 2) `shouldBe` (TmAbsDB "x" $ TmVarDB 11 12)
    it "shifts recursively in an application term" $ do
      shift 0 10 (TmAppDB (TmVarDB 0 1) (TmVarDB 0 1)) `shouldBe` (TmAppDB (TmVarDB 10 11) (TmVarDB 10 11))
  describe "substitute" $ do
    it "substitutes with 0 index" $ do
      substitute (TmVarDB 0 1) (TmVarDB 100 101) `shouldBe` TmVarDB 100 101
    it "substitutes deeper in the tree" $ do
      substitute (TmAbsDB "x" $ TmVarDB 1 2) (TmVarDB 100 101) `shouldBe` (TmAbsDB "x" $ TmVarDB 101 102)
    it "substitutes recursively in an application term" $ do
      substitute (TmAppDB (TmVarDB 0 1) (TmVarDB 0 1)) (TmVarDB 100 101) `shouldBe` (TmAppDB (TmVarDB 100 101) (TmVarDB 100 101))
  describe "eval1" $ do
    it "applies a value to an abstraction (only bound variables)" $ do
      (eval1 $ TmAppDB (TmAbsDB "x" $ TmVarDB 0 1) (TmAbsDB "y" $ TmVarDB 0 1)) `shouldBe` (Just $ TmAbsDB "y" $ TmVarDB 0 1)
    it "applies a value to an abstraction" $ do
      (eval1 $ TmAppDB (TmAbsDB "x" $ TmVarDB 0 2) (TmAbsDB "y" $ TmVarDB 1 2)) `shouldBe` (Just $ TmAbsDB "y" $ TmVarDB 1 2)
    it "evaluates right term if it's not a value" $ do
      (eval1 $ TmAppDB (TmAbsDB "x" $ TmVarDB 0 1) (TmAppDB (TmAbsDB "x" $ TmVarDB 0 1) (TmAbsDB "y" $ TmVarDB 0 1))) `shouldBe` (Just $ TmAppDB (TmAbsDB "x" $ TmVarDB 0 1) (TmAbsDB "y" $ TmVarDB 0 1))
    it "evaluates the left term first if it's not a value" $ do
      (eval1 $ TmAppDB (TmAppDB (TmAbsDB "x" $ TmVarDB 0 1) (TmAbsDB "y" $ TmVarDB 0 1)) (TmAppDB (TmAbsDB "x" $ TmVarDB 0 1) (TmAbsDB "y" $ TmVarDB 0 1))) `shouldBe` (Just $ TmAppDB (TmAbsDB "y" $ TmVarDB 0 1) (TmAppDB (TmAbsDB "x" $ TmVarDB 0 1) (TmAbsDB "y" $ TmVarDB 0 1)))
  describe "eval" $ do
    it "evaluates until it is a value" $ do
      (eval $ TmAppDB (TmAppDB (TmAbsDB "x" $ TmVarDB 0 1) (TmAbsDB "y" $ TmVarDB 0 1)) (TmAppDB (TmAbsDB "z" $ TmVarDB 0 1) (TmAbsDB "q" $ TmVarDB 0 1))) `shouldBe` (TmAbsDB "q" $ TmVarDB 0 1)

main : IO ()
main = do
  _ <- evalTest
  putStrLn $ show $ fullStep "(\\z. \\x. \\y. y z)(\\x. x)"
  putStrLn $ show $ full "(\\z. \\x. \\y. y z)(\\x. x)"
  pure ()


  --_ <- spec $ do
  --  describe "something" $ do
  --    it "is awesome" $ do
  --      (full "\\x. x") `shouldBe` (Right $ TmAbsDB "x" $ TmVarDB 0 1)
  --      (full "\\x. \\y. x y") `shouldBe` (Right $ TmAbsDB "x" $ TmAbsDB "y" $ TmAppDB (TmVarDB 1 2) (TmVarDB 0 2))
  --      (full "(\\x. x)(\\y. y y)") `shouldBe` (Right $ TmAbsDB "y" (TmAppDB (TmVarDB 0 1) (TmVarDB 0 1)))
  --      (full "(\\x. x)(\\y. y y)(\\z. z)") `shouldBe` (Right $ TmAbsDB "z" $ TmVarDB 0 1)
  --      (parse "(\\z. \\x. \\y. y z)(\\x. x)") `shouldBe` (Right $ TmAppDB (TmAbsDB "z" $ TmAbsDB "x" $ TmAbsDB "y" (TmAppDB (TmVarDB 0 3) (TmVarDB 2 3))) (TmAbsDB "x" (TmVarDB 0 1)))
  --      --(full "(\\z. \\x. \\y. y z)(\\x. x)") `shouldBe` (Right $ TmAbsDB "x" $ TmAbsDB "y" $ TmAppDB (TmVarDB 0 2) (TmAbsDB "x" (TmVarDB 0 3)))
