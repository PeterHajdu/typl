module Main

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

data Term = TmVar String
          | TmAbs String Term
          | TmApp Term Term
          | TmError

Show Term where
  show (TmVar var) = "(TmVar " ++ show var ++ ")"
  show (TmAbs var t) = "(TmAbs " ++ show var ++ ", " ++ show t ++ ")"
  show (TmApp t1 t2) = "(TmApp " ++ show t1 ++ " " ++ show t2 ++ ")"
  show TmError = "ERROR"


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
                No _ => TmError

  termParser : Parser Term
  termParser = absParser <|> appParser <|> varParser

tests : List String
tests = [
  "par1 par2",
  "par1 par2 par3",
  "\\x.x",
  "\\x . x y",
  "(\\x.x)(\\y. y) z"
  ]

parseTest : List (Either String Term)
parseTest = (Strings.parse termParser) <$> tests

main : IO ()
main = do
  _ <- traverse_ (\tm => putStrLn $ show tm) parseTest
  pure ()

