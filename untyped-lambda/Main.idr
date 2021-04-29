module Main

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings
import public Specdris.Spec
import public Control.Monad.State

data Term = TmVar Int Int
            | TmAbs String Term
            | TmApp Term Term
            | TmError String

Eq Term where
  (TmVar i d) == (TmVar i2 d2) = i == i2 && d == d2
  (TmAbs n t) == (TmAbs n2 t2) = n == n2 && t == t2
  (TmApp t1 t2) == (TmApp t12 t22) = t1 == t12 && t2 == t22
  (TmError err) == (TmError err2) = err == err2
  _ == _ = False

Show Term where
  show (TmVar var depth) = "(TmVar " ++ show var ++ ", " ++ show depth ++ ")"
  show (TmAbs name t) = "(TmAbs " ++ name ++ ", " ++ show t ++ ")"
  show (TmApp t1 t2) = "(TmApp " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (TmError cause) = "(ERROR: " ++ cause ++ ")"

data Binding =
  NameBinding String

Context : Type
Context = List Binding

index : String -> Context -> Maybe Int
index name ctx = go 0 ctx where
  go : Int -> Context -> Maybe Int
  go level ((NameBinding name2)::bindings) = if name2 == name then Just level else go (level + 1) bindings
  go _ Nil = Nothing

addNameBinding : String -> Context -> Context
addNameBinding name ctx = (NameBinding name)::ctx

identifierParser : ParserT String (State Context) String
identifierParser = pack <$> (lexeme $ some alphaNum)

varParser : ParserT String (State Context) Term
varParser = do
  name <- identifierParser
  ctx <- get
  pure $ case index name ctx of
              Just index => TmVar index (toIntNat $ List.length ctx)
              Nothing => TmError $ "unknown variable: " ++ name

safeTail : List a -> List a
safeTail (x::xs) = xs
safeTail Nil = Nil

mutual
  absParser : ParserT String (State Context) Term
  absParser = do
    _ <- lexeme $ char '\\'
    var <- identifierParser
    _ <- lexeme $ char '.'
    _ <- modify (addNameBinding var)
    t <- termParser
    _ <- modify safeTail
    pure $ TmAbs var t

  appParameterParser : ParserT String (State Context) Term
  appParameterParser = (varParser <|>| parens termParser)

  appParser : ParserT String (State Context) Term
  appParser = do
    params <- some appParameterParser
    pure $ case nonEmpty params of
                Yes _ => foldlAsFoldr TmApp (head params) (tail params)
                No _ => TmError "TmApp: not enough arguments"

  termParser : ParserT String (State Context) Term
  termParser = absParser <|> appParser <|> varParser


total
shift : Int -> Int -> Term -> Term
shift level d (TmAbs name t) = TmAbs name (shift (level + 1) d t)
shift level d (TmVar i size) = if i >= level then TmVar (i + d) (size + d) else TmVar i (size + d)
shift level d (TmApp t1 t2) = TmApp (shift level d t1) (shift level d t2)
shift level d err@(TmError err) = err

total
subst : Int -> Term -> Term -> Term
subst index (TmAbs x t1) t2 = TmAbs x (subst (index + 1) t1 t2)
subst index (TmApp t11 t12) t2 = TmApp (subst index t11 t2) (subst index t12 t2)
subst index var@(TmVar i size) t2 = if (i == index) then (shift 0 index t2) else var
subst _ err@(TmError _) _ = err

total
substitute : Term -> Term -> Term
substitute to what = subst 0 to what

isVal : Term -> Bool
isVal (TmAbs _ _) = True
isVal _ = False

total
eval1 : Term -> Maybe Term
eval1 (TmApp (TmAbs _ t1) t2@(TmAbs _ _)) = Just $ shift 0 (-1) (substitute t1 (shift 0 1 t2))
eval1 (TmApp t1@(TmAbs name t) t2) =
  let maybet2' = (eval1 t2)
   in (\t2' => TmApp t1 t2') <$> maybet2'
eval1 (TmApp t1 t2) =
  let maybet1' = (eval1 t1)
   in (\t1' => TmApp t1' t2) <$> maybet1'
eval1 _ = Nothing

eval : Term -> Term
eval t = case eval1 t of
              Just t' => if (t == t') then t else eval t'
              Nothing => t

stepeval : List Term -> Term -> List Term
stepeval acc t = case eval1 t of
                      Just t' => if (t == t') then acc else stepeval (t::acc) t'
                      Nothing => t::acc

parseWithContext : (parser    : ParserT String (State Context) Term)
            -> (source    : String)
            -> Either String Term
parseWithContext parser source =
  let res = evalState (execParserT parser (initialState Nothing source 8)) Nil
  in case res of
          MkReply _ (Success x)  => Right x
          MkReply _ (Failure es) => Left $ concat $ intersperse "\n" $ map display es

full : String -> Either String Term
full str  = eval <$> (parseWithContext termParser str)

evalTest : IO ()
evalTest = spec $ do
  describe "parser" $ do
    it "asdf" $ do
      parseWithContext termParser "\\x. x" `shouldBe` (Right $ TmAbs "x" $ TmVar 0 1)
      parseWithContext termParser "\\x. \\y. x y" `shouldBe` (Right $ TmAbs "x" $ TmAbs "y" $ TmApp (TmVar 1 2) (TmVar 0 2))
  describe "shift" $ do
    it "shifts free variables" $ do
      shift 0 10 (TmVar 0 1) `shouldBe` TmVar 10 11
      shift 0 10 (TmVar 1 2) `shouldBe` TmVar 11 12
    it "does not shift bound variables only the depth" $ do
      shift 1 10 (TmVar 0 1) `shouldBe` TmVar 0 11
      shift 2 10 (TmVar 1 2) `shouldBe` TmVar 1 12
    it "increases the depth threshold in an abstraction" $ do
      shift 0 10 (TmAbs "x" $ TmVar 0 1) `shouldBe` (TmAbs "x" $ TmVar 0 11)
      shift 0 10 (TmAbs "x" $ TmVar 1 2) `shouldBe` (TmAbs "x" $ TmVar 11 12)
    it "shifts recursively in an application term" $ do
      shift 0 10 (TmApp (TmVar 0 1) (TmVar 0 1)) `shouldBe` (TmApp (TmVar 10 11) (TmVar 10 11))
  describe "substitute" $ do
    it "substitutes with 0 index" $ do
      substitute (TmVar 0 1) (TmVar 100 101) `shouldBe` TmVar 100 101
    it "substitutes deeper in the tree" $ do
      substitute (TmAbs "x" $ TmVar 1 2) (TmVar 100 101) `shouldBe` (TmAbs "x" $ TmVar 101 102)
    it "substitutes recursively in an application term" $ do
      substitute (TmApp (TmVar 0 1) (TmVar 0 1)) (TmVar 100 101) `shouldBe` (TmApp (TmVar 100 101) (TmVar 100 101))
  describe "eval1" $ do
    it "applies a value to an abstraction (only bound variables)" $ do
      (eval1 $ TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1)) `shouldBe` (Just $ TmAbs "y" $ TmVar 0 1)
    it "applies a value to an abstraction" $ do
      (eval1 $ TmApp (TmAbs "x" $ TmVar 0 2) (TmAbs "y" $ TmVar 1 2)) `shouldBe` (Just $ TmAbs "y" $ TmVar 1 2)
    it "evaluates right term if it's not a value" $ do
      (eval1 $ TmApp (TmAbs "x" $ TmVar 0 1) (TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1))) `shouldBe` (Just $ TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1))
    it "evaluates the left term first if it's not a value" $ do
      (eval1 $ TmApp (TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1)) (TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1))) `shouldBe` (Just $ TmApp (TmAbs "y" $ TmVar 0 1) (TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1)))
  describe "eval" $ do
    it "evaluates until it is a value" $ do
      (eval $ TmApp (TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1)) (TmApp (TmAbs "z" $ TmVar 0 1) (TmAbs "q" $ TmVar 0 1))) `shouldBe` (TmAbs "q" $ TmVar 0 1)

main : IO ()
main = do
  _ <- evalTest
  putStrLn $ show $ full "(\\z. \\x. \\y. y z)(\\x. x)"
  pure ()
