module Main

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

data Term = TmTrue
           | TmFalse
           | TmIf Term Term Term
           | TmZero
           | TmSucc Term
           | TmPred Term
           | TmIsZero Term

Show Term where
  show TmTrue = "TmTrue"
  show TmFalse = "TmFalse"
  show (TmIf t1 t2 t3) = "TmIf " ++ show t1 ++ "  " ++ show t2 ++ "  " ++ show t3
  show TmZero = "TmZero"
  show (TmSucc t1) = "TmSucc " ++ show t1
  show (TmPred t1) = "TmPred " ++ show t1
  show (TmIsZero t1) = "TmIsZero " ++ show t1


mutual
  boolParser : Parser Term
  boolParser =
    (char 't' >! string "rue"  *> pure TmTrue)
    <|> (char 'f' >! string "alse" *> pure TmFalse)
    <|> ifParser

  ifParser : Parser Term
  ifParser = do
    _ <- string "if"
    t1 <- term
    _ <- string "then"
    t2 <- term
    _ <- string "else"
    t3 <- term
    pure $ TmIf t1 t2 t3

  succParser : Parser Term
  succParser = do
    _ <- string "succ"
    t <- term
    pure $ TmSucc t

  predParser : Parser Term
  predParser = do
    _ <- string "pred"
    t <- term
    pure $ TmPred t

  zeroParser : Parser Term
  zeroParser = string "zero" *> pure TmZero

  isZeroParser : Parser Term
  isZeroParser = do
    _ <- string "iszero"
    t <- term
    pure $ TmIsZero t

  numParser : Parser Term
  numParser = zeroParser <|> succParser <|> predParser <|> isZeroParser

  term' : Parser Term
  term' = boolParser <|> numParser

  term : Parser Term
  term = spaces *> term' <* spaces

eval1 : Term -> Maybe Term
eval1 (TmIf TmTrue t2 t3) = Just t2
eval1 (TmIf TmFalse t2 t3) = Just t3
eval1 (TmIf t1 t2 t3) = (\t1' => TmIf t1' t2 t3) <$> eval1 t1
eval1 (TmPred TmZero) = Just TmZero
eval1 (TmPred (TmSucc t)) = Just t
eval1 (TmPred t) = TmPred <$> eval1 t
eval1 (TmSucc t) = TmSucc <$> eval1 t
eval1 (TmIsZero TmZero) = Just TmTrue
eval1 (TmIsZero (TmSucc _)) = Just TmFalse
eval1 (TmIsZero t) = TmIsZero <$> eval1 t
eval1 _ = Nothing

eval : Term -> Term
eval t = case eval1 t of
              Just t => eval t
              Nothing => t

tests : List String
tests = [
  "true",
  "false",
  "iszero true",
  "if if true then true else false then zero else if true then false else true",
  "if if false then false else true then iszero pred succ succ zero else false",
  "if if false then false else true then succ pred succ succ zero else false"]

parseTest : List (Either String Term)
parseTest = (Strings.parse term) <$> tests

termTest : List (Either String Term)
termTest = (map eval) <$> parseTest

main : IO ()
main = do
  putStrLn "parse"
  traverse_ (\t => putStrLn $ show t) parseTest
  putStrLn "eval"
  traverse_ (\t => putStrLn $ show t) termTest

