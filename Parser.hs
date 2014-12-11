{-# LANGUAGE OverloadedStrings #-}

module Parser(
  parseTopLevel,
  parseTopLevels,
  parseSExpr
  ) where

import Control.Applicative
import Data.Attoparsec.Text as PC
import Data.Char
import qualified Data.Text as T hiding (zipWith)
import Types

ss :: Parser ()
ss = skipSpace

between a b mp = char a *> ss *> mp <* ss <* char b

inParens p = between '(' ')' p

parseSymbol :: Parser Symbol
parseSymbol = do
  a <- PC.satisfy (PC.inClass symbolChars)
  as <- PC.takeWhile (PC.inClass $ symbolChars ++ "0123456789")
  return $ T.cons a as
  where symbolChars = "-.abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
                      ++ "=*/+_?$!@~><&%'#`;:{}"

parseEmptyList :: Parser SExpr
parseEmptyList = char '(' *> ss *> char ')' *> pure (Appl [])

parseString :: Parser Atom
parseString = Str . T.pack <$> (char '"' *> chars <* char '"')
  where chars = many' $ escaped <|> PC.satisfy (\c -> isAscii c && c /= '"')
        escaped = char '\\' >> choice (zipWith escapedChar codes replacements)
        escapedChar code replacement = char code >> return replacement
        codes        = ['b',  'n',  'f',  'r',  't',  '\\', '"', '/']
        replacements = ['\b', '\n', '\f', '\r', '\t', '\\', '"', '/']

parseNumber :: Parser Atom
parseNumber = toKLNumber <$> number
    where toKLNumber (I i) = N (KI i)
          toKLNumber (D d) = N (KD d)

parseParamList :: Parser ParamList
parseParamList = between '(' ')' $ sepBy' parseSymbol ss

parseSymbolOrBool :: Parser SExpr
parseSymbolOrBool = do
  sym <- parseSymbol
  return $ case sym of
    "true"  -> Lit (B True)
    "false" -> Lit (B False)
    _ -> Sym sym

parseAtom :: Parser SExpr
parseAtom = Lit <$> (parseNumber <|> parseString) <|> parseSymbolOrBool

parseAppl :: Parser SExpr
parseAppl = inParens $ Appl <$> sepBy' parseSExpr ss

parseLambda :: Parser SExpr
parseLambda = inParens $ Lambda <$> (string "lambda" *> ss *> parseSymbol <* ss)
              <*> (parseSExpr <* ss)

parseFreeze :: Parser SExpr
parseFreeze = inParens $ Freeze <$> (string "freeze" *> ss *> parseSExpr <* ss)

parseLet :: Parser SExpr
parseLet = inParens $ Let <$> (string "let" *> ss *> parseSymbol <* ss)
           <*> parseSExpr <*> (ss *> parseSExpr <* ss)

parseIf :: Parser SExpr
parseIf = inParens $ If <$> (string "if" *> ss *> parseSExpr <* ss)
           <*> parseSExpr <*> (ss *> parseSExpr <* ss)           

parseAnd :: Parser SExpr
parseAnd = inParens $ And <$> (string "and" *> ss *> parseSExpr <* ss)
           <*> (parseSExpr <* ss)           

parseOr :: Parser SExpr
parseOr = inParens $ Or <$> (string "or" *> ss *> parseSExpr <* ss)
           <*> (parseSExpr <* ss)           

parseCond :: Parser SExpr
parseCond = inParens $ Cond <$> (string "cond" *> ss *> sepBy' parseClause ss)
    where parseClause = inParens $ (,) <$> parseSExpr <*> (ss *> parseSExpr)

parseSExpr :: Parser SExpr
parseSExpr = parseEmptyList <|> parseFreeze <|> parseLet <|> parseLambda
             <|> parseIf <|> parseAnd <|> parseOr <|> parseCond <|> parseAppl
             <|> parseAtom

parseDefun :: Parser TopLevel
parseDefun = inParens $ Defun <$> (string "defun" *> ss *> parseSymbol <* ss)
             <*> parseParamList <* ss <*> parseSExpr

parseTopLevel :: Parser TopLevel
parseTopLevel = SE <$> parseEmptyList <|> parseDefun <|> SE <$> parseSExpr

parseTopLevels :: Parser [TopLevel]
parseTopLevels = sepBy' (parseDefun <|> SE <$> parseSExpr) ss
