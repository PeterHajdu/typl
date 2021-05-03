module Main

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings
import public Specdris.Spec
import public Control.Monad.State

data Term = TmVar Int Int
            | TmAbs String Term
            | TmApp Term Term
            | TmTrue
            | TmFalse
            | TmIf Term Term Term
            | TmError String

Eq Term where
  (TmVar i d) == (TmVar i2 d2) = i == i2 && d == d2
  (TmAbs n t) == (TmAbs n2 t2) = n == n2 && t == t2
  (TmApp t1 t2) == (TmApp t12 t22) = t1 == t12 && t2 == t22
  (TmError err) == (TmError err2) = err == err2
  TmFalse == TmFalse = True
  TmTrue == TmTrue = True
  (TmIf a b c) == (TmIf a2 b2 c2) = a == a2 && b == b2 && c == c2
  _ == _ = False

Show Term where
  show (TmVar var depth) = "(TmVar " ++ show var ++ ", " ++ show depth ++ ")"
  show (TmAbs name t) = "(TmAbs " ++ name ++ ", " ++ show t ++ ")"
  show (TmApp t1 t2) = "(TmApp " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (TmError cause) = "(ERROR: " ++ cause ++ ")"
  show TmTrue = "TmTrue"
  show TmFalse = "TmFalse"
  show (TmIf a b c) = "(If " ++ show a ++ " then " ++ show b ++ " else " ++ show c ++ ")"

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
identifierParser = do
  identifier <- pack <$> (lexeme $ some alphaNum)
  pure identifier

trueParser : ParserT String (State Context) Term
trueParser = (lexeme $ string "true") *> pure TmTrue

falseParser : ParserT String (State Context) Term
falseParser = (lexeme $ string "false") *> pure TmFalse

boolParser : ParserT String (State Context) Term
boolParser = trueParser <|> falseParser

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
  ifParser : ParserT String (State Context) Term
  ifParser = do
    _ <- lexeme $ string "if"
    guard <- parens termParser
    _ <- lexeme $ string "then"
    t1 <- parens termParser
    _ <- lexeme $ string "else"
    t2 <- parens $ termParser
    pure $ TmIf guard t1 t2

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
  termParser = ifParser <|> boolParser <|> absParser <|> appParser <|> varParser

total
shift : Int -> Int -> Term -> Term
shift level d (TmAbs name t) = TmAbs name (shift (level + 1) d t)
shift level d (TmVar i size) = if i >= level then TmVar (i + d) (size + d) else TmVar i (size + d)
shift level d (TmApp t1 t2) = TmApp (shift level d t1) (shift level d t2)
shift level d err@(TmError err) = err
shift _ _ TmTrue = TmTrue
shift _ _ TmFalse = TmFalse
shift level d (TmIf a b c) = (TmIf (shift level d a) (shift level d b) (shift level d c))

total
subst : Int -> Term -> Term -> Term
subst index (TmAbs x t1) t2 = TmAbs x (subst (index + 1) t1 t2)
subst index (TmApp t11 t12) t2 = TmApp (subst index t11 t2) (subst index t12 t2)
subst index var@(TmVar i size) t2 = if (i == index) then (shift 0 index t2) else var
subst index TmTrue _ = TmTrue
subst index TmFalse _ = TmFalse
subst index (TmIf a b c) t = TmIf (subst index a t) (subst index b t) (subst index c t)
subst _ err@(TmError _) _ = err

total
substitute : Term -> Term -> Term
substitute to what = subst 0 to what

isVal : Term -> Bool
isVal (TmAbs _ _) = True
isVal _ = False

total
eval1 : Term -> Maybe Term
eval1 (TmIf TmTrue t1 t2) = Just t1
eval1 (TmIf TmFalse t1 t2) = Just t2
eval1 (TmIf (TmAbs _ _) _ _) = (Just $ TmError "guard of an if term should be a boolean")
eval1 (TmIf g t1 t2) =
  let maybeg' = (eval1 g)
   in (\g' => TmIf g' t1 t2) <$> maybeg'
eval1 (TmApp (TmAbs _ t1) t2@(TmAbs _ _)) = Just $ shift 0 (-1) (substitute t1 (shift 0 1 t2))
eval1 (TmApp (TmAbs _ t1) TmTrue) = Just $ shift 0 (-1) (substitute t1 TmTrue)
eval1 (TmApp (TmAbs _ t1) TmFalse) = Just $ shift 0 (-1) (substitute t1 TmFalse)
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
    it "parses booleans" $ do
      parseWithContext termParser "true" `shouldBe` (Right $ TmTrue)
      parseWithContext termParser "false" `shouldBe` (Right $ TmFalse)
    it "parses if statements" $ do
      parseWithContext termParser "if (true) then (true) else (false)" `shouldBe` (Right $ TmIf TmTrue TmTrue TmFalse)
      parseWithContext termParser "if (\\x.x) then (true) else (false)" `shouldBe` (Right $ TmIf (TmAbs "x" $ TmVar 0 1) TmTrue TmFalse)
      parseWithContext termParser "if (\\x.x) then (\\y.y) else (false)" `shouldBe` (Right $ TmIf (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1) TmFalse)
      parseWithContext termParser "if (\\x.x) then (\\y.y) else (\\z.z)" `shouldBe` (Right $ TmIf (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1) (TmAbs "z" $ TmVar 0 1))
      parseWithContext termParser "\\z. \\q. if (\\x. x) then (\\y. y) else (z q)" `shouldBe` (Right $ TmAbs "z" $ TmAbs "q" $ TmIf (TmAbs "x" $ TmVar 0 3) (TmAbs "y" $ TmVar 0 3) (TmApp (TmVar 1 2) (TmVar 0 2)))
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
    it "leaves true and false terms as it is" $ do
      shift 0 10 TmTrue `shouldBe` TmTrue
      shift 0 10 TmFalse `shouldBe` TmFalse
    it "shifts recursively in an If term" $ do
      shift 0 10 (TmIf (TmVar 0 1) (TmVar 0 1) (TmVar 0 1)) `shouldBe` (TmIf (TmVar 10 11) (TmVar 10 11) (TmVar 10 11))

  describe "substitute" $ do
    it "substitutes with 0 index" $ do
      substitute (TmVar 0 1) (TmVar 100 101) `shouldBe` TmVar 100 101
    it "substitutes deeper in the tree" $ do
      substitute (TmAbs "x" $ TmVar 1 2) (TmVar 100 101) `shouldBe` (TmAbs "x" $ TmVar 101 102)
    it "substitutes recursively in an application term" $ do
      substitute (TmApp (TmVar 0 1) (TmVar 0 1)) (TmVar 100 101) `shouldBe` (TmApp (TmVar 100 101) (TmVar 100 101))
    it "leaves true and false terms as they are" $ do
      substitute TmTrue (TmVar 100 101) `shouldBe` TmTrue
      substitute TmFalse (TmVar 100 101) `shouldBe` TmFalse
    it "substitutes recursively in an If term" $ do
      substitute (TmIf (TmVar 0 1) (TmVar 0 1) (TmVar 0 1)) (TmVar 100 101) `shouldBe` (TmIf (TmVar 100 101) (TmVar 100 101) (TmVar 100 101))

  describe "eval1" $ do
    it "applies a value to an abstraction (only bound variables)" $ do
      (eval1 $ TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1)) `shouldBe` (Just $ TmAbs "y" $ TmVar 0 1)
    it "applies a value to an abstraction" $ do
      (eval1 $ TmApp (TmAbs "x" $ TmVar 0 2) (TmAbs "y" $ TmVar 1 2)) `shouldBe` (Just $ TmAbs "y" $ TmVar 1 2)
    it "evaluates right term if it's not a value" $ do
      (eval1 $ TmApp (TmAbs "x" $ TmVar 0 1) (TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1))) `shouldBe` (Just $ TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1))
    it "evaluates the left term first if it's not a value" $ do
      (eval1 $ TmApp (TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1)) (TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1))) `shouldBe` (Just $ TmApp (TmAbs "y" $ TmVar 0 1) (TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1)))
    it "uses the second term if the guard is true in an if term" $ do
      (eval1 $ TmIf TmTrue (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1)) `shouldBe` (Just (TmAbs "x" $ TmVar 0 1))
    it "uses the third term if the guard is false in an if term" $ do
      (eval1 $ TmIf TmFalse (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1)) `shouldBe` (Just (TmAbs "y" $ TmVar 0 1))
    it "evaluates the guard of an if term if it's not a value" $ do
      (eval1 $ TmIf (TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1)) TmTrue TmTrue) `shouldBe` (Just $ TmIf (TmAbs "y" $ TmVar 0 1) TmTrue TmTrue)
    it "evaluates to an error if the guard is an abstraction" $ do
      (eval1 $ TmIf (TmAbs "x" $ TmVar 0 1) TmTrue TmTrue) `shouldBe` (Just $ TmError "guard of an if term should be a boolean")
    it "substitutes true" $ do
      (eval1 $ TmApp (TmAbs "x" $ TmVar 0 1) TmTrue) `shouldBe` (Just $ TmTrue)
    it "substitutes false" $ do
      (eval1 $ TmApp (TmAbs "x" $ TmVar 0 1) TmFalse) `shouldBe` (Just $ TmFalse)
  describe "eval" $ do
    it "evaluates until it is a value" $ do
      (eval $ TmApp (TmApp (TmAbs "x" $ TmVar 0 1) (TmAbs "y" $ TmVar 0 1)) (TmApp (TmAbs "z" $ TmVar 0 1) (TmApp (TmAbs "q" $ TmVar 0 1) TmTrue))) `shouldBe` TmTrue

main : IO ()
main = evalTest

