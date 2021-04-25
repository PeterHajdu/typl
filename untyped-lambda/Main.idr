module Main

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

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

tests : List String
tests = [
  "par1 par2",
  "par1 par2 par3",
  "\\x.x",
  "\\x . x y",
  "(\\x.x)(\\y. y) z",
  "(\\x.(\\y. x y))(\\z. z)(\\x. x (\\y. x y))"
  ]

parseTest : List (Either String Term)
parseTest = (Strings.parse termParser) <$> tests

dbTest : List TermDB
dbTest = toDB 0 Nil <$> rights parseTest

main : IO ()
main = do
  _ <- traverse_ (\tm => putStrLn $ show tm) parseTest
  _ <- traverse_ (\tm => putStrLn $ show tm) dbTest
  pure ()

