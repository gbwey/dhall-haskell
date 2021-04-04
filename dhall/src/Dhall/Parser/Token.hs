{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

-- | Parse Dhall tokens. Even though we don't have a tokenizer per-se this
---  module is useful for keeping some small parsing utilities.
module Dhall.Parser.Token (
    validCodepoint,
    whitespace,
    lineComment,
    blockComment,
    nonemptyWhitespace,
    bashEnvironmentVariable,
    posixEnvironmentVariable,
    ComponentType(..),
    text,
    char,
    file_,
    label,
    anyLabelOrSome,
    anyLabel,
    labels,
    httpRaw,
    hexdig,
    identifier,
    hexNumber,
    doubleLiteral,
    doubleInfinity,
    nonZeroLiteral,
    nonZeroLiteralWithoutBang,
    atLiteral,
    rationalLiteral,
    dateTimeLiteral,
    dateTimeParse,
    naturalLiteral,
    integerLiteral,

    _SZ,
    _SS,
    _Optional,
    _if,
    _then,
    _else,
    _let,
    _in,
    _as,
    _using,
    _merge,
    _toMap,
    _assert,
    _Some,
    _None,

    _NonZero,
    _NonZeroShow,
    _NonZeroClamp,
    _NonZeroDiv,
    _NonZeroMod,
    _NonZeroLog,
    _NonZeroAdd,
    _NonZeroMultiply,
    _NonZeroToNatural,
    _NonZeroToInteger,
    _NonZeroParse,

    _DateTime,
    _DateTimeShow,
    _DateTimeParse,
    _DateTimeFromSeconds,
    _DateTimeToSeconds,

    _DateTimeAddYears,
    _DateTimeAddMonths,
    _DateTimeAddDays,
    _DateTimeFromWeek,
    _DateTimeToWeek,
    _DateTimeToDate,
    _DateTimeFromDate,
    _DateTimeLastDayOfMonth,

    _DateTimeGetJulianDay,
    _DateTimeSetJulianDay,

    _Regex,
    _RegexShow,
    _RegexMatch,
    _RegexScan,
    _RegexSplit,
    _RegexReplace,
    _RegexReplix,
    _RegexParse,
    _RegexToText,

    _Rational,
    _RationalShow,
    _RationalFromDouble,
    _RationalToDouble,
    _RationalFromRational,
    _RationalParse,

    _NaturalFold,
    _NaturalBuild,
    _NaturalIsZero,
    _NaturalEven,
    _NaturalOdd,
    _NaturalToInteger,
    _NaturalShow,
    _NaturalParse,
    _NaturalToBits,
    _NaturalSubtract,
    _NaturalGcd,
    _IntegerAdd,
    _IntegerMultiply,
    _IntegerAnd,
    _IntegerXor,
    _IntegerClamp,
    _IntegerNegate,
    _IntegerShow,
    _IntegerParse,
    _IntegerToDouble,
    _DoubleShow,
    _DoubleParse,
    _ListBuild,
    _ListFold,
    _ListLength,
    _ListHead,
    _ListLast,
    _ListIndexed,
    _ListReverse,
    _ListPermutations,
    _ListChoose,
    _ListFixedFromList,
    _ListFixedToList,
    _ListFixedHead,
    _ListFixedTail,
    _SymFromText,
    _SymToText,
    _SSFromNonZero,
    _SSToNonZero,
    _SSToNatural,
    _SSAdd,
    _SSSubtract,
    _SSEqual,
    _SSLessThan,
    _Proof,
    _Prf,
    _ProofToBool,
    _ProofFromBool,
    _PVoid,
    _PVoidUndefined,
    _PVoidError,
    _PVoidKindUndefined,
    _Bool,
    _Natural,
    _Integer,
    _Double,
    _Text,
    _TextShow,
    _TextToLower,
    _TextToUpper,
    _TextUnpack,
    _TextPack,
    _TextToList,
    _TextLength,
    _TextCompare,
    _List,
    _ListFixed,
    _True,
    _False,
    _NaN,
    _Type,
    _Kind,
    _Sort,
    _Location,
    _equal,
    _or,
    _plus,
    _percent,
    _textAppend,
    _listAppend,
    _and,
    _times,
    _doubleEqual,
    _notEqual,
    _dot,
    _openBrace,
    _closeBrace,
    _openBracket,
    _closeBracket,
    _openAngle,
    _closeAngle,
    _bar,
    _comma,
    _openParens,
    _closeParens,
    _colon,
    _at,
    _equivalent,
    _missing,
    _importAlt,
    _combine,
    _combineTypes,
    _prefer,
    _lambda,
    _forall,
    _arrow,
    _doubleColon,
    _with,
    ) where

import Dhall.Parser.Combinators

import Control.Applicative     (Alternative (..), optional)
import Data.Bits               ((.&.))
import Data.Functor            (void, ($>))
import Data.Text               (Text)
import Dhall.Set               (Set)
import Dhall.Syntax
import Text.Parser.Combinators (choice, try, (<?>))

import qualified Control.Monad
import qualified Data.Char                  as Char
import qualified Data.Foldable
import qualified Data.HashSet
import qualified Data.List                  as List
import qualified Data.List.NonEmpty
import Data.Ratio ((%))
import qualified Data.Scientific            as Scientific
import qualified Data.Text
import qualified Data.Time
import qualified Dhall.Set
import qualified Text.Megaparsec
import qualified Text.Megaparsec.Char.Lexer
import qualified Text.Parser.Char
import qualified Text.Parser.Combinators
import qualified Text.Parser.Token

import Numeric.Natural (Natural)


-- | Returns `True` if the given `Int` is a valid Unicode codepoint
validCodepoint :: Int -> Bool
validCodepoint c =
    not (category == Char.Surrogate
      || c .&. 0xFFFE == 0xFFFE
      || c .&. 0xFFFF == 0xFFFF)
  where
    category = Char.generalCategory (Char.chr c)

{-| Parse 0 or more whitespace characters (including comments)

    This corresponds to the @whsp@ rule in the official grammar
-}
whitespace :: Parser ()
whitespace = Text.Parser.Combinators.skipMany whitespaceChunk

{-| Parse 1 or more whitespace characters (including comments)

    This corresponds to the @whsp1@ rule in the official grammar
-}
nonemptyWhitespace :: Parser ()
nonemptyWhitespace = Text.Parser.Combinators.skipSome whitespaceChunk

alpha :: Char -> Bool
alpha c = ('\x41' <= c && c <= '\x5A') || ('\x61' <= c && c <= '\x7A')

digit :: Char -> Bool
digit c = '\x30' <= c && c <= '\x39'

alphaNum :: Char -> Bool
alphaNum c = alpha c || digit c

{-| Parse a hex digit (uppercase or lowercase)

    This corresponds to the @HEXDIG@ rule in the official grammar
-}
hexdig :: Char -> Bool
hexdig c =
        ('0' <= c && c <= '9')
    ||  ('A' <= c && c <= 'F')
    ||  ('a' <= c && c <= 'f')

signPrefix :: Num a => Parser (a -> a)
signPrefix = (do
    let positive = fmap (\_ -> id    ) (char '+')
    let negative = fmap (\_ -> negate) (char '-')
    positive <|> negative ) <?> "sign"

{-| Parse a `NonZero` literal

    This corresponds to the @nonzero-literal@ rule from the official grammar
-}
nonZeroLiteral :: Parser NonZero
nonZeroLiteral = do
    _ <- char '!' <?> "bang"
    nonZeroLiteralWithoutBang

nonZeroLiteralWithoutBang :: Parser NonZero
nonZeroLiteralWithoutBang = (do
    a <- naturalLiteral
--    Control.Monad.guard (a > 0)
    Control.Monad.when (a <= 0) $ fail "cannot be zero"
    return (NonZeroC a) ) <?> "literal"

atLiteral :: Parser NonZero
atLiteral = (do
    a <- Text.Megaparsec.Char.Lexer.decimal
    Control.Monad.when (a <= 0) $ fail "cannot be zero"
    return (NonZeroC a) ) <?> "literal"



{-| Parse a `Rational` literal

    This corresponds to the @Rational-literal@ rule from the official grammar
-}
rationalLiteral :: Parser Rational
rationalLiteral = (do
    a <- integerLiteral
    _ <- whitespace
    _ <- _percent
    _ <- whitespace
    NonZeroC b <- nonZeroLiteral
    --Control.Monad.guard (b > 0)
    return (a % fromIntegral b) ) <?> "literal"

{-| Parse a `DateTime` literal

    This corresponds to the @datetime-literal@ rule from the official grammar
-}
dateTimeLiteral :: Parser DateTime
dateTimeLiteral = (do
    s <- Data.Text.unpack <$> Dhall.Parser.Combinators.takeWhile1 (\c -> Char.isDigit c || c == '-' || c == 'T' || c == ':' || c == '+')
    case dateTimeParse s of
      Left e -> fail e
      Right d -> pure d) <?> "literal"

dateTimeParse :: String -> Either String DateTime
dateTimeParse s' =
  let (s,pos) = case s' of
                  x:xs | x == '-' -> (xs, False)
                       | x == '+' -> (xs, True)
                  _ -> (s', True)
      f fmt = Data.Time.parseTimeM True Data.Time.defaultTimeLocale fmt s
  in do
       ldt <- case Data.Foldable.asum
               (map f [ "T%H:%M:%S",         "%H:%M:%S"
                      , "T%H:%M",            "%H:%M"
                      , "T%H"
                      , "%Y-%m-%dT%H:%M:%S", "%Y-%m-%dT%H:%M",  "%Y-%m-%dT%H", "%Y-%m-%d"
                      , "%Y-%mT%H:%M:%S",    "%Y-%mT%H:%M",     "%Y-%mT%H",    "%Y-%m"
                      , "%YT%H:%M:%S",       "%YT%H:%M",        "%YT%H",       "%Y"
                      ]
               ) of
                 Just x -> Right x
                 Nothing -> Left "invalid datetime format"
       let tm = Data.Time.localTimeOfDay ldt
       Control.Monad.unless (Data.Time.todHour tm < 24) $ Left "hours are out of range"
       Control.Monad.unless (Data.Time.todMin tm < 60) $ Left "minutes are out of range"
       Control.Monad.unless (Data.Time.todSec tm < 60) $ Left "seconds are out of range"
{-
       Control.Monad.guard (Data.Time.todHour tm < 24)
       Control.Monad.guard (Data.Time.todMin tm < 60)
       Control.Monad.guard (Data.Time.todSec tm < 60)
-}
       let udt = Data.Time.localTimeToUTC Data.Time.utc ldt
       let r =if pos then udt
              else
                let (a,b,c) = Data.Time.toGregorian (Data.Time.utctDay udt)
                    d = Data.Time.fromGregorian (-a) b c
                in udt { Data.Time.utctDay = d }
       pure (utcToDateTime r)


{-| Parse a `Double` literal

    This corresponds to the @double-literal@ rule from the official grammar
-}
doubleLiteral :: Parser Double
doubleLiteral = (do
    -- We don't use `Text.Parser.Token.double` since that consumes trailing
    -- whitespace and there is no whitespace-free alternative.  See:
    --
    -- https://github.com/dhall-lang/dhall-haskell/pull/1646
    -- https://github.com/dhall-lang/dhall-haskell/pull/1647
    --
    -- We also don't use `Text.Megaparsec.Char.Lexer.float` because that
    -- transitively depends on `Data.Char.toTitle` which is broken on older
    -- versions of GHCJS that we still support.  See:
    --
    -- https://github.com/dhall-lang/dhall-haskell/pull/1681
    -- https://github.com/ghcjs/ghcjs-base/issues/62
    --
    -- Also, hand-writing the parser code for `Double` literals helps to better
    -- ensure that we follow the standard exactly as written.
    sign <- signPrefix <|> pure id

    x <- Text.Parser.Token.decimal

    let alternative0 = do
            y <- fraction

            e <- exponent' <|> pure 1

            return ((fromInteger x + y) * e)

    let alternative1 = do
            expo <- exponent'

            return (fromInteger x * expo)

    n <- alternative0 <|> alternative1

    return (sign (Scientific.toRealFloat n)) ) <?> "literal"
  where
    fraction = do
        _ <- Text.Parser.Char.char '.'

        digits <- some Text.Parser.Char.digit

        let snoc y d =
              y + Scientific.scientific (fromIntegral (Char.digitToInt d)) (Scientific.base10Exponent y - 1)

        return (List.foldl' snoc 0 digits)

    exponent' = do
        _ <- Text.Parser.Char.oneOf "eE"

        sign <- signPrefix <|> pure id

        x <- Text.Parser.Token.decimal

        return (Scientific.scientific 1 (fromInteger (sign x)))

{-| Parse a signed @Infinity@

    This corresponds to the @minus-infinity-literal@ and @plus-infinity-literal@
    rules from the official grammar
-}
doubleInfinity :: Parser Double
doubleInfinity = (do
    let negative = fmap (\_ -> negate) (char '-')
    sign <- negative <|> pure id
    a <- text "Infinity" >> return (1.0/0.0)
    return (sign a) ) <?> "literal"

{-| Parse an `Integer` literal

    This corresponds to the @integer-literal@ rule from the official grammar
-}
integerLiteral :: Parser Integer
integerLiteral = (do
    sign <- signPrefix
    a    <- naturalLiteral
    return (sign (fromIntegral a)) ) <?> "literal"

{-| Parse a `Natural` literal

    This corresponds to the @natural-literal@ rule from the official grammar
-}
naturalLiteral :: Parser Natural
naturalLiteral = (do
    a <-    try (char '0' >> char 'x' >> Text.Megaparsec.Char.Lexer.hexadecimal)
        <|> try (char '0' >> char 'o' >> Text.Megaparsec.Char.Lexer.octal)
        <|> try (char '0' >> char 'b' >> Text.Megaparsec.Char.Lexer.binary)
        <|> decimal
        <|> (char '0' $> 0)
    return a ) <?> "literal"
  where
    decimal = do
        n <- headDigit
        ns <- many tailDigit
        return (mkNum (n:ns))
      where
        headDigit = decimalDigit nonZeroDigit <?> "non-zero digit"
          where
            nonZeroDigit c = '1' <= c && c <= '9'

        tailDigit = decimalDigit digit <?> "digit"

        decimalDigit predicate = do
            c <- Text.Parser.Char.satisfy predicate
            return (fromIntegral (Char.ord c - Char.ord '0'))

        mkNum = Data.Foldable.foldl' step 0
          where
            step acc x = acc * 10 + x


{-| Parse an identifier (i.e. a variable or built-in)

    Variables can have an optional index to disambiguate shadowed variables

    This corresponds to the @identifier@ rule from the official grammar
-}
identifier :: Parser Var
identifier = do
    x <- label

    let indexed = try $ do
            whitespace
            _at
            whitespace
            n <- naturalLiteral
            return (fromIntegral n)

    n <- indexed <|> pure 0
    return (V x n)

whitespaceChunk :: Parser ()
whitespaceChunk =
    choice
        [ void (Dhall.Parser.Combinators.takeWhile1 predicate)
        , void (Text.Parser.Char.text "\r\n" <?> "newline")
        , void lineComment
        , void blockComment
        ] <?> "whitespace"
  where
    predicate c = c == ' ' || c == '\t' || c == '\n'

-- | Parse a hexademical number and convert to the corresponding `Int`
hexNumber :: Parser Int
hexNumber = choice [ hexDigit, hexUpper, hexLower ]
  where
    hexDigit = do
        c <- Text.Parser.Char.satisfy predicate
        return (Char.ord c - Char.ord '0')
      where
        predicate c = '0' <= c && c <= '9'

    hexUpper = do
        c <- Text.Parser.Char.satisfy predicate
        return (10 + Char.ord c - Char.ord 'A')
      where
        predicate c = 'A' <= c && c <= 'F'

    hexLower = do
        c <- Text.Parser.Char.satisfy predicate
        return (10 + Char.ord c - Char.ord 'a')
      where
        predicate c = 'a' <= c && c <= 'f'

-- | Parse a Dhall's single-line comment, starting from `--` and until the
--   last character of the line /before/ the end-of-line character
lineComment :: Parser Text
lineComment = do
    _ <- text "--"

    let predicate c = ('\x20' <= c && c <= '\x10FFFF') || c == '\t'

    commentText <- Dhall.Parser.Combinators.takeWhile predicate

    endOfLine

    return ("--" <> commentText)
  where
    endOfLine =
        (   void (Text.Parser.Char.char '\n'  )
        <|> void (Text.Parser.Char.text "\r\n")
        ) <?> "newline"

-- | Parsed text doesn't include opening braces
blockComment :: Parser Text
blockComment = do
    _ <- text "{-"
    c <- blockCommentContinue
    pure ("{-" <> c <> "-}")

blockCommentChunk :: Parser Text
blockCommentChunk =
    choice
        [ blockComment  -- Nested block comment
        , characters
        , character
        , endOfLine
        ]
  where
    characters = (Dhall.Parser.Combinators.takeWhile1 predicate)
      where
        predicate c =
                '\x20' <= c && c <= '\x10FFFF' && c /= '-' && c /= '{'
            ||  c == '\n'
            ||  c == '\t'

    character = (Dhall.Parser.Combinators.satisfy predicate)
      where
        predicate c = '\x20' <= c && c <= '\x10FFFF' || c == '\n' || c == '\t'

    endOfLine = (Text.Parser.Char.text "\r\n" <?> "newline")

blockCommentContinue :: Parser Text
blockCommentContinue = endOfComment <|> continue
  where
    endOfComment = void (text "-}") *> pure ""

    continue = do
        c <- blockCommentChunk
        c' <- blockCommentContinue
        pure (c <> c')

simpleLabel :: Bool -> Parser Text
simpleLabel allowReserved = try $ do
    c    <- Text.Parser.Char.satisfy headCharacter
    rest <- Dhall.Parser.Combinators.takeWhile tailCharacter
    let t = Data.Text.cons c rest
    let isNotAKeyword = not $ t `Data.HashSet.member` reservedKeywords
    let isNotAReservedIdentifier = not $ t `Data.HashSet.member` reservedIdentifiers
    Control.Monad.guard (isNotAKeyword && (allowReserved || isNotAReservedIdentifier))
    return t

headCharacter :: Char -> Bool
headCharacter c = alpha c || c == '_'

tailCharacter :: Char -> Bool
tailCharacter c = alphaNum c || c == '_' || c == '-' || c == '/'

backtickLabel :: Parser Text
backtickLabel = do
    _ <- char '`'
    t <- Dhall.Parser.Combinators.takeWhile predicate
    _ <- char '`'
    return t
  where
    predicate c =
            '\x20' <= c && c <= '\x5F'
        ||  '\x61' <= c && c <= '\x7E'

{-| Parse a braced sequence of comma-separated labels

    For example, this is used to parse the record projection syntax

    This corresponds to the @labels@ rule in the official grammar
-}
labels :: Parser (Set Text)
labels = do
    _openBrace

    whitespace

    xs <- nonEmptyLabels <|> emptyLabels

    _ <- optional (_comma *> whitespace)

    return xs
  where
    emptyLabels = do
        try (optional (_comma *> whitespace) *> _closeBrace)

        pure Dhall.Set.empty

    nonEmptyLabels = do
        x  <- try (optional (_comma *> whitespace) *> anyLabelOrSome)

        whitespace

        xs <- many (try (_comma *> whitespace *> anyLabelOrSome) <* whitespace)

        _ <- optional (_comma *> whitespace)

        _closeBrace

        noDuplicates (x : xs)

{-| Parse a label (e.g. a variable\/field\/alternative name)

    Rejects labels that match built-in names (e.g. @Natural/even@)

    This corresponds to the @nonreserved-label@ rule in the official grammar
-}
label :: Parser Text
label = backtickLabel <|> simpleLabel False <?> "label"

{-| Same as `label` except that built-in names are allowed

    This corresponds to the @any-label@ rule in the official grammar
-}
anyLabel :: Parser Text
anyLabel = (do
    t <- backtickLabel <|> simpleLabel True
    return t ) <?> "any label"

{-| Same as `anyLabel` except that `Some` is allowed

    This corresponds to the @any-label-or-some@ rule in the official grammar
-}

anyLabelOrSome :: Parser Text
anyLabelOrSome = try anyLabel <|> ("Some" <$ _Some)

{-| Parse a valid Bash environment variable name

    This corresponds to the @bash-environment-variable@ rule in the official
    grammar
-}
bashEnvironmentVariable :: Parser Text
bashEnvironmentVariable = satisfy predicate0 <> star (satisfy predicate1)
  where
    predicate0 c = alpha c || c == '_'

    predicate1 c = alphaNum c || c == '_'

{-| Parse a valid POSIX environment variable name, which permits a wider range
    of characters than a Bash environment variable name

    This corresponds to the @posix-environment-variable@ rule in the official
    grammar
-}
posixEnvironmentVariable :: Parser Text
posixEnvironmentVariable = plus posixEnvironmentVariableCharacter

posixEnvironmentVariableCharacter :: Parser Text
posixEnvironmentVariableCharacter =
    escapeCharacter <|> satisfy predicate1
  where
    escapeCharacter = do
        _ <- char '\\'

        c <- Text.Parser.Char.satisfy (`elem` ("\"\\abfnrtv" :: String))

        case c of
            '"'  -> return "\""
            '\\' -> return "\\"
            'a'  -> return "\a"
            'b'  -> return "\b"
            'f'  -> return "\f"
            'n'  -> return "\n"
            'r'  -> return "\r"
            't'  -> return "\t"
            'v'  -> return "\v"
            _    -> empty

    predicate1 c =
            ('\x20' <= c && c <= '\x21')
        ||  ('\x23' <= c && c <= '\x3C')
        ||  ('\x3E' <= c && c <= '\x5B')
        ||  ('\x5D' <= c && c <= '\x7E')

quotedPathCharacter :: Char -> Bool
quotedPathCharacter c =
        ('\x20' <= c && c <= '\x21')
    ||  ('\x23' <= c && c <= '\x2E')
    ||  ('\x30' <= c && c <= '\x10FFFF')

{-| The `pathComponent` function uses this type to distinguish whether to parse
    a URL path component or a file path component
-}
data ComponentType = URLComponent | FileComponent

-- | Parse a path component
pathComponent :: ComponentType -> Parser Text
pathComponent componentType = do
    _ <- "/" :: Parser Text

    let pathData =
            case componentType of
                FileComponent ->
                    Text.Megaparsec.takeWhile1P Nothing Dhall.Syntax.pathCharacter
                URLComponent ->
                    star pchar

    let quotedPathData = do
            _ <- char '"'
            t <- Text.Megaparsec.takeWhile1P Nothing quotedPathCharacter
            _ <- char '"'
            return t

    case componentType of
        FileComponent -> quotedPathData <|> pathData
        URLComponent -> pathData

-- | Parse a `File`
file_ :: ComponentType -> Parser File
file_ componentType = do
    let emptyPath =
            case componentType of
                URLComponent  -> pure (pure "")
                FileComponent -> empty

    path <- Data.List.NonEmpty.some1 (pathComponent componentType) <|> emptyPath

    let directory = Directory (reverse (Data.List.NonEmpty.init path))
    let file      = Data.List.NonEmpty.last path

    return (File {..})

scheme_ :: Parser Scheme
scheme_ =
        ("http" :: Parser Text)
    *>  ((("s" :: Parser Text) *> pure HTTPS) <|> pure HTTP)
    <*  ("://" :: Parser Text)

{-| Parse an HTTP(S) URL without trailing whitespace

    This corresponds to the @http-raw@ rule in the official grammar
-}
httpRaw :: Parser URL
httpRaw = do
    scheme    <- scheme_
    authority <- authority_
    path      <- file_ URLComponent
    query     <- optional (("?" :: Parser Text) *> query_)

    let headers = Nothing

    return (URL {..})

authority_ :: Parser Text
authority_ = option (try (userinfo <> "@")) <> host <> option (":" <> port)

userinfo :: Parser Text
userinfo = star (satisfy predicate <|> pctEncoded)
  where
    predicate c = unreserved c || subDelims c || c == ':'

host :: Parser Text
host = choice [ ipLiteral, try ipV4Address, domain ]

port :: Parser Text
port = star (satisfy digit)

ipLiteral :: Parser Text
ipLiteral = "[" <> (ipV6Address <|> ipVFuture) <> "]"

ipVFuture :: Parser Text
ipVFuture = "v" <> plus (satisfy hexdig) <> "." <> plus (satisfy predicate)
  where
    predicate c = unreserved c || subDelims c || c == ':'

ipV6Address :: Parser Text
ipV6Address =
    choice
        [ try alternative0
        , try alternative1
        , try alternative2
        , try alternative3
        , try alternative4
        , try alternative5
        , try alternative6
        , try alternative7
        ,     alternative8
        ]
  where
    alternative0 = count 6 (h16 <> ":") <> ls32

    alternative1 = "::" <> count 5 (h16 <> ":") <> ls32

    alternative2 = option h16 <> "::" <> count 4 (h16 <> ":") <> ls32

    alternative3 =
            option (h16 <> range 0 1 (try (":" <> h16)))
        <>  "::"
        <>  count 3 (h16 <> ":")
        <>  ls32

    alternative4 =
            option (h16 <> range 0 2 (try (":" <> h16)))
        <>  "::"
        <>  count 2 (h16 <> ":")
        <>  ls32

    alternative5 =
            option (h16 <> range 0 3 (try (":" <> h16)))
        <>  "::"
        <>  h16
        <>  ":"
        <>  ls32

    alternative6 =
        option (h16 <> range 0 4 (try (":" <> h16))) <> "::" <> ls32

    alternative7 =
        option (h16 <> range 0 5 (try (":" <> h16))) <> "::" <> h16

    alternative8 =
        option (h16 <> range 0 6 (try (":" <> h16))) <> "::"

h16 :: Parser Text
h16 = range 1 3 (satisfy hexdig)

ls32 :: Parser Text
ls32 = try (h16 <> ":" <> h16) <|> ipV4Address

ipV4Address :: Parser Text
ipV4Address = decOctet <> "." <> decOctet <> "." <> decOctet <> "." <> decOctet

decOctet :: Parser Text
decOctet =
    choice
        [ try alternative4
        , try alternative3
        , try alternative2
        , try alternative1
        ,     alternative0
        ]
  where
    alternative0 = satisfy digit

    alternative1 = satisfy predicate <> satisfy digit
      where
        predicate c = '\x31' <= c && c <= '\x39'

    alternative2 = "1" <> count 2 (satisfy digit)

    alternative3 = "2" <> satisfy predicate <> satisfy digit
      where
        predicate c = '\x30' <= c && c <= '\x34'

    alternative4 = "25" <> satisfy predicate
      where
        predicate c = '\x30' <= c && c <= '\x35'

domain :: Parser Text
domain = domainLabel <> star ("." <> domainLabel ) <> option "."

domainLabel :: Parser Text
domainLabel = plus alphaNum_ <> star (plus "-" <> plus alphaNum_)
  where
    alphaNum_ = satisfy alphaNum

pchar :: Parser Text
pchar = satisfy predicate <|> pctEncoded
  where
    predicate c = unreserved c || subDelims c || c == ':' || c == '@'

query_ :: Parser Text
query_ = star (pchar <|> satisfy predicate)
  where
    predicate c = c == '/' || c == '?'

pctEncoded :: Parser Text
pctEncoded = "%" <> count 2 (satisfy hexdig)

subDelims :: Char -> Bool
subDelims c = c `elem` ("!$&'*+;=" :: String)

unreserved :: Char -> Bool
unreserved c =
    alphaNum c || c == '-' || c == '.' || c == '_' || c == '~'

{-| A variation on `Text.Parser.Char.text` that doesn't quote the expected
    in error messages
-}
text :: Data.Text.Text -> Parser Text
text t = Text.Parser.Char.text t <?> Data.Text.unpack t
{-# INLINE text #-}

{-| A variation on `Text.Parser.Char.char` that doesn't quote the expected
    token in error messages
-}
char :: Char -> Parser Char
char c = Text.Parser.Char.char c <?> [ c ]
{-# INLINE char #-}

reserved :: Data.Text.Text -> Parser ()
reserved x = void (text x)

reservedChar :: Char -> Parser ()
reservedChar c = void (char c)

builtin :: Data.Text.Text -> Parser ()
builtin x = reserved x <?> "built-in"
{-# INLINE builtin #-}

operator :: Data.Text.Text -> Parser ()
operator x = reserved x <?> "operator"
{-# INLINE operator #-}

operatorChar :: Char -> Parser ()
operatorChar x = reservedChar x <?> "operator"
{-# INLINE operatorChar #-}

keyword :: Data.Text.Text -> Parser ()
keyword x = try (void (text x)) <?> "keyword"

{-| Parse the @if@ keyword

    This corresponds to the @if@ rule from the official grammar
-}
_if :: Parser ()
_if = keyword "if"

{-| Parse the @then@ keyword

    This corresponds to the @then@ rule from the official grammar
-}
_then :: Parser ()
_then = keyword "then"

{-| Parse the @else@ keyword

    This corresponds to the @else@ rule from the official grammar
-}
_else :: Parser ()
_else = keyword "else"

{-| Parse the @let@ keyword

    This corresponds to the @let@ rule from the official grammar
-}
_let :: Parser ()
_let = keyword "let"

{-| Parse the @in@ keyword

    This corresponds to the @in@ rule from the official grammar
-}
_in :: Parser ()
_in = keyword "in"

{-| Parse the @as@ keyword

    This corresponds to the @as@ rule from the official grammar
-}
_as :: Parser ()
_as = keyword "as"

{-| Parse the @using@ keyword

    This corresponds to the @using@ rule from the official grammar
-}
_using :: Parser ()
_using = keyword "using"

{-| Parse the @merge@ keyword

    This corresponds to the @merge@ rule from the official grammar
-}
_merge :: Parser ()
_merge = keyword "merge"

{-| Parse the @toMap@ keyword

    This corresponds to the @toMap@ rule from the official grammar
-}
_toMap :: Parser ()
_toMap = keyword "toMap"

{-| Parse the @assert@ keyword

    This corresponds to the @assert@ rule from the official grammar
-}
_assert :: Parser ()
_assert = keyword "assert"

-- | Parse the @with@ keyword
_with :: Parser ()
_with = keyword "with"

{-| Parse the @Some@ built-in

    This corresponds to the @Some@ rule from the official grammar
-}
_Some :: Parser ()
_Some = keyword "Some"

{-| Parse the @None@ built-in

    This corresponds to the @None@ rule from the official grammar
-}
_None :: Parser ()
_None = builtin "None"


{-| Parse the @NonZero/show@ built-in

    This corresponds to the @NonZero-show@ rule from the official grammar
-}
_NonZeroShow :: Parser ()
_NonZeroShow = builtin "NonZero/show"

{-| Parse the @NonZero/clamp@ built-in

    This corresponds to the @NonZero-clamp@ rule from the official grammar
-}
_NonZeroClamp :: Parser ()
_NonZeroClamp = builtin "NonZero/clamp"

{-| Parse the @NonZero/div@ built-in

    This corresponds to the @NonZero-div@ rule from the official grammar
-}
_NonZeroDiv :: Parser ()
_NonZeroDiv = builtin "NonZero/div"

{-| Parse the @NonZero/mod@ built-in

    This corresponds to the @NonZero-mod@ rule from the official grammar
-}
_NonZeroMod :: Parser ()
_NonZeroMod = builtin "NonZero/mod"

{-| Parse the @NonZero/log@ built-in

    This corresponds to the @NonZero-log@ rule from the official grammar
-}
_NonZeroLog :: Parser ()
_NonZeroLog = builtin "NonZero/log"

{-| Parse the @NonZero/add@ built-in

    This corresponds to the @NonZero-add@ rule from the official grammar
-}
_NonZeroAdd :: Parser ()
_NonZeroAdd = builtin "NonZero/add"

{-| Parse the @NonZero/multiply@ built-in

    This corresponds to the @NonZero-multiply@ rule from the official grammar
-}
_NonZeroMultiply :: Parser ()
_NonZeroMultiply = builtin "NonZero/multiply"

{-| Parse the @NonZero/toNatural@ built-in

    This corresponds to the @NonZero-toNatural@ rule from the official grammar
-}
_NonZeroToNatural :: Parser ()
_NonZeroToNatural = builtin "NonZero/toNatural"

{-| Parse the @NonZero/toInteger@ built-in

    This corresponds to the @NonZero-toInteger@ rule from the official grammar
-}
_NonZeroToInteger :: Parser ()
_NonZeroToInteger = builtin "NonZero/toInteger"

{-| Parse the @NonZero/parse@ built-in

    This corresponds to the @NonZero-parse@ rule from the official grammar
-}
_NonZeroParse :: Parser ()
_NonZeroParse = builtin "NonZero/parse"

{-| Parse the @DateTime/show@ built-in

    This corresponds to the @DateTime-show@ rule from the official grammar
-}
_DateTimeShow :: Parser ()
_DateTimeShow = builtin "DateTime/show"

{-| Parse the @DateTime/parse@ built-in

    This corresponds to the @DateTime-parse@ rule from the official grammar
-}
_DateTimeParse :: Parser ()
_DateTimeParse = builtin "DateTime/parse"

{-| Parse the @DateTime/fromSeconds@ built-in

    This corresponds to the @DateTime-fromSeconds@ rule from the official grammar
-}
_DateTimeFromSeconds :: Parser ()
_DateTimeFromSeconds = builtin "DateTime/fromSeconds"

{-| Parse the @DateTime/toSeconds@ built-in

    This corresponds to the @DateTime-toSeconds@ rule from the official grammar
-}
_DateTimeToSeconds :: Parser ()
_DateTimeToSeconds = builtin "DateTime/toSeconds"

{-| Parse the @DateTime/addYears@ built-in

    This corresponds to the @DateTime-addYears@ rule from the official grammar
-}
_DateTimeAddYears :: Parser ()
_DateTimeAddYears = builtin "DateTime/addYears"

{-| Parse the @DateTime/addMonths@ built-in

    This corresponds to the @DateTime-addMonths@ rule from the official grammar
-}
_DateTimeAddMonths :: Parser ()
_DateTimeAddMonths = builtin "DateTime/addMonths"

{-| Parse the @DateTime/addDays@ built-in

    This corresponds to the @DateTime-addDays@ rule from the official grammar
-}
_DateTimeAddDays :: Parser ()
_DateTimeAddDays = builtin "DateTime/addDays"

{-| Parse the @DateTime/fromWeek@ built-in

    This corresponds to the @DateTime-fromWeek@ rule from the official grammar
-}
_DateTimeFromWeek :: Parser ()
_DateTimeFromWeek = builtin "DateTime/fromWeek"

{-| Parse the @DateTime/toWeek@ built-in

    This corresponds to the @DateTime-toWeek@ rule from the official grammar
-}
_DateTimeToWeek :: Parser ()
_DateTimeToWeek = builtin "DateTime/toWeek"

{-| Parse the @DateTime/toDate@ built-in

    This corresponds to the @DateTime-toDate@ rule from the official grammar
-}
_DateTimeToDate :: Parser ()
_DateTimeToDate = builtin "DateTime/toDate"

{-| Parse the @DateTime/fromDate@ built-in

    This corresponds to the @DateTime-fromDate@ rule from the official grammar
-}
_DateTimeFromDate :: Parser ()
_DateTimeFromDate = builtin "DateTime/fromDate"


{-| Parse the @DateTime/lastDayOfMonth@ built-in

    This corresponds to the @DateTime-lastDayOfMonth@ rule from the official grammar
-}
_DateTimeLastDayOfMonth :: Parser ()
_DateTimeLastDayOfMonth = builtin "DateTime/lastDayOfMonth"


{-| Parse the @DateTime/getJulianDay@ built-in

    This corresponds to the @DateTime-getJulianDay@ rule from the official grammar
-}
_DateTimeGetJulianDay :: Parser ()
_DateTimeGetJulianDay = builtin "DateTime/getJulianDay"

{-| Parse the @DateTime/setJulianDay@ built-in

    This corresponds to the @DateTime-setJulianDay@ rule from the official grammar
-}
_DateTimeSetJulianDay :: Parser ()
_DateTimeSetJulianDay = builtin "DateTime/setJulianDay"



{-| Parse the @Regex/show@ built-in

    This corresponds to the @Regex-show@ rule from the official grammar
-}
_RegexShow :: Parser ()
_RegexShow = builtin "Regex/show"

{-| Parse the @Regex/match@ built-in

    This corresponds to the @Regex-match@ rule from the official grammar
-}
_RegexMatch :: Parser ()
_RegexMatch = builtin "Regex/match"

{-| Parse the @Regex/scan@ built-in

    This corresponds to the @Regex-scan@ rule from the official grammar
-}
_RegexScan :: Parser ()
_RegexScan = builtin "Regex/scan"

{-| Parse the @Regex/split@ built-in

    This corresponds to the @Regex-split@ rule from the official grammar
-}
_RegexSplit :: Parser ()
_RegexSplit = builtin "Regex/split"

{-| Parse the @Regex/replace@ built-in

    This corresponds to the @Regex-replace@ rule from the official grammar
-}
_RegexReplace :: Parser ()
_RegexReplace = builtin "Regex/replace"

{-| Parse the @Regex/replix@ built-in

    This corresponds to the @Regex-replix@ rule from the official grammar
-}
_RegexReplix :: Parser ()
_RegexReplix = builtin "Regex/replix"

{-| Parse the @Regex/parse@ built-in

    This corresponds to the @Regex-parse@ rule from the official grammar
-}
_RegexParse :: Parser ()
_RegexParse = builtin "Regex/parse"

{-| Parse the @Regex/toText@ built-in

    This corresponds to the @Regex-toText@ rule from the official grammar
-}
_RegexToText :: Parser ()
_RegexToText = builtin "Regex/toText"



{-| Parse the @Rational/show@ built-in

    This corresponds to the @Rational-show@ rule from the official grammar
-}
_RationalShow :: Parser ()
_RationalShow = builtin "Rational/show"

{-| Parse the @Rational/fromDouble@ built-in

    This corresponds to the @Rational-fromDouble@ rule from the official grammar
-}
_RationalFromDouble :: Parser ()
_RationalFromDouble = builtin "Rational/fromDouble"

{-| Parse the @Rational/toDouble@ built-in

    This corresponds to the @Rational-toDouble@ rule from the official grammar
-}
_RationalToDouble :: Parser ()
_RationalToDouble = builtin "Rational/toDouble"

{-| Parse the @Rational/fromRational@ built-in

    This corresponds to the @Rational-fromRational@ rule from the official grammar
-}
_RationalFromRational :: Parser ()
_RationalFromRational = builtin "Rational/fromRational"

{-| Parse the @Rational/parse@ built-in

    This corresponds to the @Rational-parse@ rule from the official grammar
-}
_RationalParse :: Parser ()
_RationalParse = builtin "Rational/parse"



{-| Parse the @Natural/fold@ built-in

    This corresponds to the @Natural-fold@ rule from the official grammar
-}
_NaturalFold :: Parser ()
_NaturalFold = builtin "Natural/fold"

{-| Parse the @Natural/build@ built-in

    This corresponds to the @Natural-build@ rule from the official grammar
-}
_NaturalBuild :: Parser ()
_NaturalBuild = builtin "Natural/build"

{-| Parse the @Natural/isZero@ built-in

    This corresponds to the @Natural-isZero@ rule from the official grammar
-}
_NaturalIsZero :: Parser ()
_NaturalIsZero = builtin "Natural/isZero"

{-| Parse the @Natural/even@ built-in

    This corresponds to the @Natural-even@ rule from the official grammar
-}
_NaturalEven :: Parser ()
_NaturalEven = builtin "Natural/even"

{-| Parse the @Natural/odd@ built-in

    This corresponds to the @Natural-odd@ rule from the official grammar
-}
_NaturalOdd :: Parser ()
_NaturalOdd = builtin "Natural/odd"

{-| Parse the @Natural/toInteger@ built-in

    This corresponds to the @Natural-toInteger@ rule from the official grammar
-}
_NaturalToInteger :: Parser ()
_NaturalToInteger = builtin "Natural/toInteger"

{-| Parse the @Natural/show@ built-in

    This corresponds to the @Natural-show@ rule from the official grammar
-}
_NaturalShow :: Parser ()
_NaturalShow = builtin "Natural/show"

{-| Parse the @Natural/parse@ built-in

    This corresponds to the @Natural-parse@ rule from the official grammar
-}
_NaturalParse :: Parser ()
_NaturalParse = builtin "Natural/parse"
{-| Parse the @Natural/toBits@ built-in

    This corresponds to the @Natural-toBits@ rule from the official grammar
-}
_NaturalToBits :: Parser ()
_NaturalToBits = builtin "Natural/toBits"
{-| Parse the @Natural/subtract@ built-in

    This corresponds to the @Natural-subtract@ rule from the official grammar
-}
_NaturalSubtract :: Parser ()
_NaturalSubtract = builtin "Natural/subtract"

{-| Parse the @Natural/gcd@ built-in

    This corresponds to the @Natural-gcde@ rule from the official grammar
-}
_NaturalGcd :: Parser ()
_NaturalGcd = builtin "Natural/gcd"

{-| Parse the @Integer/add@ built-in

    This corresponds to the @Integer-add@ rule from the official grammar
-}
_IntegerAdd :: Parser ()
_IntegerAdd = builtin "Integer/add"

{-| Parse the @Integer/multiply@ built-in

    This corresponds to the @Integer-multiply@ rule from the official grammar
-}
_IntegerMultiply :: Parser ()
_IntegerMultiply = builtin "Integer/multiply"

{-| Parse the @Integer/and@ built-in

    This corresponds to the @Integer-and@ rule from the official grammar
-}
_IntegerAnd :: Parser ()
_IntegerAnd = builtin "Integer/and"

{-| Parse the @Integer/xor@ built-in

    This corresponds to the @Integer-xor@ rule from the official grammar
-}
_IntegerXor :: Parser ()
_IntegerXor = builtin "Integer/xor"

{-| Parse the @Integer/clamp@ built-in

    This corresponds to the @Integer-clamp@ rule from the official grammar
-}
_IntegerClamp :: Parser ()
_IntegerClamp = builtin "Integer/clamp"

{-| Parse the @Integer/negate@ built-in

    This corresponds to the @Integer-negate@ rule from the official grammar
-}
_IntegerNegate :: Parser ()
_IntegerNegate = builtin "Integer/negate"

{-| Parse the @Integer/show@ built-in

    This corresponds to the @Integer-show@ rule from the official grammar
-}
_IntegerShow :: Parser ()
_IntegerShow = builtin "Integer/show"

{-| Parse the @Integer/parse@ built-in

    This corresponds to the @Integer-parse@ rule from the official grammar
-}
_IntegerParse :: Parser ()
_IntegerParse = builtin "Integer/parse"

{-| Parse the @Integer/toDouble@ built-in

    This corresponds to the @Integer-toDouble@ rule from the official grammar
-}
_IntegerToDouble :: Parser ()
_IntegerToDouble = builtin "Integer/toDouble"

{-| Parse the @Double/show@ built-in

    This corresponds to the @Double-show@ rule from the official grammar
-}
_DoubleShow :: Parser ()
_DoubleShow = builtin "Double/show"

{-| Parse the @Double/parse@ built-in

    This corresponds to the @Double-parse@ rule from the official grammar
-}
_DoubleParse :: Parser ()
_DoubleParse = builtin "Double/parse"

{-| Parse the @List/build@ built-in

    This corresponds to the @List-build@ rule from the official grammar
-}
_ListBuild :: Parser ()
_ListBuild = builtin "List/build"

{-| Parse the @List/fold@ built-in

    This corresponds to the @List-fold@ rule from the official grammar
-}
_ListFold :: Parser ()
_ListFold = builtin "List/fold"

{-| Parse the @List/length@ built-in

    This corresponds to the @List-length@ rule from the official grammar
-}
_ListLength :: Parser ()
_ListLength = builtin "List/length"

{-| Parse the @List/head@ built-in

    This corresponds to the @List-head@ rule from the official grammar
-}
_ListHead :: Parser ()
_ListHead = builtin "List/head"

{-| Parse the @List/last@ built-in

    This corresponds to the @List-last@ rule from the official grammar
-}
_ListLast :: Parser ()
_ListLast = builtin "List/last"

{-| Parse the @List/indexed@ built-in

    This corresponds to the @List-indexed@ rule from the official grammar
-}
_ListIndexed :: Parser ()
_ListIndexed = builtin "List/indexed"

{-| Parse the @List/reverse@ built-in

    This corresponds to the @List-reverse@ rule from the official grammar
-}
_ListReverse :: Parser ()
_ListReverse = builtin "List/reverse"

{-| Parse the @List/permutations@ built-in

    This corresponds to the @List-permutationse@ rule from the official grammar
-}
_ListPermutations :: Parser ()
_ListPermutations = builtin "List/permutations"

{-| Parse the @List/choose@ built-in

    This corresponds to the @List-choosee@ rule from the official grammar
-}
_ListChoose :: Parser ()
_ListChoose = builtin "List/choose"

{-| Parse the @ListFixed/fromList@ built-in

    This corresponds to the @ListFixed-fromList@ rule from the official grammar
-}
_ListFixedFromList :: Parser ()
_ListFixedFromList = builtin "ListFixed/fromList"

{-| Parse the @ListFixed/toList@ built-in

    This corresponds to the @ListFixed-toList@ rule from the official grammar
-}
_ListFixedToList :: Parser ()
_ListFixedToList = builtin "ListFixed/toList"

{-| Parse the @ListFixed/head@ built-in

    This corresponds to the @ListFixed-head@ rule from the official grammar
-}
_ListFixedHead :: Parser ()
_ListFixedHead = builtin "ListFixed/head"

{-| Parse the @ListFixed/tail@ built-in

    This corresponds to the @ListFixed-tail@ rule from the official grammar
-}
_ListFixedTail :: Parser ()
_ListFixedTail = builtin "ListFixed/tail"

{-| Parse the @Sym/fromText@ built-in

    This corresponds to the @Sym-fromText@ rule from the official grammar
-}
_SymFromText :: Parser ()
_SymFromText = builtin "Sym/fromText"

{-| Parse the @Sym/toText@ built-in

    This corresponds to the @Sym-toText@ rule from the official grammar
-}
_SymToText :: Parser ()
_SymToText = builtin "Sym/toText"

{-| Parse the @SS/fromNonZero@ built-in

    This corresponds to the @SS-fromNonZero@ rule from the official grammar
-}
_SSFromNonZero :: Parser ()
_SSFromNonZero = builtin "SS/fromNonZero"

{-| Parse the @SS/toNonZero@ built-in

    This corresponds to the @SS-toNonZero@ rule from the official grammar
-}
_SSToNonZero :: Parser ()
_SSToNonZero = builtin "SS/toNonZero"

{-| Parse the @SS/toNatural@ built-in

    This corresponds to the @SS-toNatural@ rule from the official grammar
-}
_SSToNatural :: Parser ()
_SSToNatural = builtin "SS/toNatural"

{-| Parse the @SS/add@ built-in

    This corresponds to the @SS-add@ rule from the official grammar
-}
_SSAdd :: Parser ()
_SSAdd = builtin "SS/add"

{-| Parse the @SS/add@ built-in

    This corresponds to the @SS-subtract@ rule from the official grammar
-}
_SSSubtract :: Parser ()
_SSSubtract = builtin "SS/subtract"

{-| Parse the @SS/equal@ built-in

    This corresponds to the @SS-equal@ rule from the official grammar
-}
_SSEqual :: Parser ()
_SSEqual = builtin "SS/equal"

{-| Parse the @SS/lessThan@ built-in

    This corresponds to the @SS-lessThan@ rule from the official grammar
-}
_SSLessThan :: Parser ()
_SSLessThan = builtin "SS/lessThan"

{-| Parse the @Bool@ built-in

    This corresponds to the @Bool@ rule from the official grammar
-}
_Bool :: Parser ()
_Bool = builtin "Bool"

{-| Parse the @SZ@ built-in

    This corresponds to the @SZ@ rule from the official grammar
-}
_SZ :: Parser ()
_SZ = builtin "SZ"

{-| Parse the @SS@ built-in

    This corresponds to the @SS@ rule from the official grammar
-}
_SS :: Parser ()
_SS = builtin "SS"

{-| Parse the @Proof@ built-in

    This corresponds to the @Proof@ rule from the official grammar
-}
_Proof :: Parser ()
_Proof = builtin "Proof"

{-| Parse the @Prf@ built-in

    This corresponds to the @Prf@ rule from the official grammar
-}
_Prf :: Parser ()
_Prf = builtin "Prf"

{-| Parse the @Proof/toBool@ built-in

    This corresponds to the @Proof-toBool@ rule from the official grammar
-}
_ProofToBool :: Parser ()
_ProofToBool = builtin "Proof/toBool"

{-| Parse the @Proof/fromBool@ built-in

    This corresponds to the @Proof-fromBool@ rule from the official grammar
-}
_ProofFromBool :: Parser ()
_ProofFromBool = builtin "Proof/fromBool"

{-| Parse the @PVoid@ built-in

    This corresponds to the @PVoid@ rule from the official grammar
-}
_PVoid :: Parser ()
_PVoid = builtin "PVoid"

{-| Parse the @PVoid/undefined@ built-in

    This corresponds to the @PVoid-undefined@ rule from the official grammar
-}
_PVoidUndefined :: Parser ()
_PVoidUndefined = builtin "PVoid/undefined"

{-| Parse the @PVoid/error@ built-in

    This corresponds to the @PVoid-error@ rule from the official grammar
-}
_PVoidError :: Parser ()
_PVoidError = builtin "PVoid/error"

{-| Parse the @PVoid/kindUndefined@ built-in

    This corresponds to the @PVoid-kindUndefined@ rule from the official grammar
-}
_PVoidKindUndefined :: Parser ()
_PVoidKindUndefined = builtin "PVoid/kindUndefined"

{-| Parse the @Optional@ built-in

    This corresponds to the @Optional@ rule from the official grammar
-}
_Optional :: Parser ()
_Optional = builtin "Optional"

{-| Parse the @NonZero@ built-in

    This corresponds to the @NonZero@ rule from the official grammar
-}
_NonZero :: Parser ()
_NonZero = builtin "NonZero"

{-| Parse the @DateTime@ built-in

    This corresponds to the @DateTime@ rule from the official grammar
-}
_DateTime :: Parser ()
_DateTime = builtin "DateTime"

{-| Parse the @Regex@ built-in

    This corresponds to the @Regex@ rule from the official grammar
-}
_Regex :: Parser ()
_Regex = builtin "Regex"

{-| Parse the @Rational@ built-in

    This corresponds to the @Rational@ rule from the official grammar
-}
_Rational :: Parser ()
_Rational = builtin "Rational"

{-| Parse the @Natural@ built-in

    This corresponds to the @Natural@ rule from the official grammar
-}
_Natural :: Parser ()
_Natural = builtin "Natural"

{-| Parse the @Integer@ built-in

    This corresponds to the @Integer@ rule from the official grammar
-}
_Integer :: Parser ()
_Integer = builtin "Integer"

{-| Parse the @Double@ built-in

    This corresponds to the @Double@ rule from the official grammar
-}
_Double :: Parser ()
_Double = builtin "Double"

{-| Parse the @Text@ built-in

    This corresponds to the @Text@ rule from the official grammar
-}
_Text :: Parser ()
_Text = builtin "Text"

{-| Parse the @Text/show@ built-in

    This corresponds to the @Text-show@ rule from the official grammar
-}
_TextShow :: Parser ()
_TextShow = builtin "Text/show"

{-| Parse the @Text/toLower@ built-in

    This corresponds to the @Text-toLower@ rule from the official grammar
-}
_TextToLower :: Parser ()
_TextToLower = builtin "Text/toLower"

{-| Parse the @Text/toUpper@ built-in

    This corresponds to the @Text-toUpper@ rule from the official grammar
-}
_TextToUpper :: Parser ()
_TextToUpper = builtin "Text/toUpper"

{-| Parse the @Text/unpack@ built-in

    This corresponds to the @Text-unpack@ rule from the official grammar
-}
_TextUnpack :: Parser ()
_TextUnpack = builtin "Text/unpack"

{-| Parse the @Text/pack@ built-in

    This corresponds to the @Text-pack@ rule from the official grammar
-}
_TextPack :: Parser ()
_TextPack = builtin "Text/pack"

{-| Parse the @Text/toList@ built-in

    This corresponds to the @Text-toList@ rule from the official grammar
-}
_TextToList :: Parser ()
_TextToList = builtin "Text/toList"

{-| Parse the @Text/length@ built-in

    This corresponds to the @Text-length@ rule from the official grammar
-}
_TextLength :: Parser ()
_TextLength = builtin "Text/length"

{-| Parse the @Text/compare@ built-in

    This corresponds to the @Text-compare@ rule from the official grammar
-}
_TextCompare :: Parser ()
_TextCompare = builtin "Text/compare"

{-| Parse the @List@ built-in

    This corresponds to the @List@ rule from the official grammar
-}
_List :: Parser ()
_List = builtin "List"

{-| Parse the @ListFixed@ built-in

    This corresponds to the @ListFixed@ rule from the official grammar
-}
_ListFixed :: Parser ()
_ListFixed = builtin "ListFixed"

{-| Parse the @True@ built-in

    This corresponds to the @True@ rule from the official grammar
-}
_True :: Parser ()
_True = builtin "True"

{-| Parse the @False@ built-in

    This corresponds to the @False@ rule from the official grammar
-}
_False :: Parser ()
_False = builtin "False"

{-| Parse a @NaN@ literal

    This corresponds to the @NaN@ rule from the official grammar
-}
_NaN :: Parser ()
_NaN = builtin "NaN"

{-| Parse the @Type@ built-in

    This corresponds to the @Type@ rule from the official grammar
-}
_Type :: Parser ()
_Type = builtin "Type"

{-| Parse the @Kind@ built-in

    This corresponds to the @Kind@ rule from the official grammar
-}
_Kind :: Parser ()
_Kind = builtin "Kind"

{-| Parse the @Sort@ built-in

    This corresponds to the @Sort@ rule from the official grammar
-}
_Sort :: Parser ()
_Sort = builtin "Sort"

{-| Parse the @Location@ keyword

    This corresponds to the @Location@ rule from the official grammar
-}
_Location :: Parser ()
_Location = builtin "Location"

-- | Parse the @=@ symbol
_equal :: Parser ()
_equal = reservedChar '='

-- | Parse the @||@ symbol
_or :: Parser ()
_or = operator "||"

-- | Parse the @+@ symbol
_plus :: Parser ()
_plus = operatorChar '+'

-- | Parse the @%@ symbol
_percent :: Parser ()
_percent = operatorChar '%'

-- | Parse the @++@ symbol
_textAppend :: Parser ()
_textAppend = operator "++"

-- | Parse the @#@ symbol
_listAppend :: Parser ()
_listAppend = operatorChar '#'

-- | Parse the @&&@ symbol
_and :: Parser ()
_and = operator "&&"

-- | Parse the @*@ symbol
_times :: Parser ()
_times = operatorChar '*'

-- | Parse the @==@ symbol
_doubleEqual :: Parser ()
_doubleEqual = operator "=="

-- | Parse the @!=@ symbol
_notEqual :: Parser ()
_notEqual = operator "!="

-- | Parse the @.@ symbol
_dot :: Parser ()
_dot = operatorChar '.'

-- | Parse the @{@ symbol
_openBrace :: Parser ()
_openBrace = reservedChar '{'

-- | Parse the @}@ symbol
_closeBrace :: Parser ()
_closeBrace = reservedChar '}'

-- | Parse the @[@] symbol
_openBracket :: Parser ()
_openBracket = reservedChar '['

-- | Parse the @]@ symbol
_closeBracket :: Parser ()
_closeBracket = reservedChar ']'

-- | Parse the @<@ symbol
_openAngle :: Parser ()
_openAngle = reservedChar '<'

-- | Parse the @>@ symbol
_closeAngle :: Parser ()
_closeAngle = reservedChar '>'

-- | Parse the @|@ symbol
_bar :: Parser ()
_bar = reservedChar '|'

-- | Parse the @,@ symbol
_comma :: Parser ()
_comma = reservedChar ',' <?> "\',\'"

-- | Parse the @(@ symbol
_openParens :: Parser ()
_openParens = reservedChar '('

-- | Parse the @)@ symbol
_closeParens :: Parser ()
_closeParens = reservedChar ')'

-- | Parse the @:@ symbol
_colon :: Parser ()
_colon = reservedChar ':'

-- | Parse the @\@@ symbol
_at :: Parser ()
_at = reservedChar '@' <?> "\"@\""

-- | Parse the equivalence symbol (@===@ or @≡@)
_equivalent :: Parser ()
_equivalent = (void (char '≡' <?> "\"≡\"") <|> void (text "===")) <?> "operator"

-- | Parse the @missing@ keyword
_missing :: Parser ()
_missing =
        keyword "missing"
    *>  Text.Megaparsec.notFollowedBy (Text.Parser.Char.satisfy tailCharacter)

-- | Parse the @?@ symbol
_importAlt :: Parser ()
_importAlt = operatorChar '?'

-- | Parse the record combine operator (@/\\@ or @∧@)
_combine :: Parser ()
_combine = (void (char '∧' <?> "\"∧\"") <|> void (text "/\\")) <?> "operator"

-- | Parse the record type combine operator (@//\\\\@ or @⩓@)
_combineTypes :: Parser ()
_combineTypes = (void (char '⩓' <?> "\"⩓\"") <|> void (text "//\\\\")) <?> "operator"

-- | Parse the record \"prefer\" operator (@//@ or @⫽@)
_prefer :: Parser ()
_prefer = (void (char '⫽' <?> "\"⫽\"") <|> void (text "//")) <?> "operator"

-- | Parse a lambda (@\\@ or @λ@)
_lambda :: Parser ()
_lambda = void (Text.Parser.Char.satisfy predicate) <?> "\\"
  where
    predicate 'λ'  = True
    predicate '\\' = True
    predicate _    = False

-- | Parse a forall (@forall@ or @∀@)
_forall :: Parser ()
_forall = (void (char '∀' <?> "\"∀\"") <|> void (text "forall")) <?> "forall"

-- | Parse a right arrow (@->@ or @→@)
_arrow :: Parser ()
_arrow = (void (char '→' <?> "\"→\"") <|> void (text "->")) <?> "->"

-- | Parse a double colon (@::@)
_doubleColon :: Parser ()
_doubleColon = operator "::"
