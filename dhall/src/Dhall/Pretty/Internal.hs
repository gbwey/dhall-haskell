{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

{-# OPTIONS_GHC -Wall #-}

{-| This module provides internal pretty-printing utilities which are used by
    other modules but are not part of the public facing API
-}

module Dhall.Pretty.Internal (
      Ann(..)
    , annToAnsiStyle
    , prettyExpr
    , prettySrcExpr

    , CharacterSet(..)
    , prettyCharacterSet

    , prettyVar
    , pretty_
    , escapeText_
    , escapeEnvironmentVariable
    , prettyEnvironmentVariable

    , prettyConst
    , escapeLabel
    , prettyLabel
    , prettyAnyLabel
    , prettyLabels

    , prettyNonZero
    , prettyDateTime
    , prettyRegex
    , prettyRational

    , prettyNatural
    , prettyNumber
    , prettyInt
    , prettyDouble
    , prettyToStrictText
    , prettyToString
    , layout
    , layoutOpts

    , docToStrictText

    , builtin
    , keyword
    , literal
    , operator

    , colon
    , comma
    , dot
    , equals
    , forall
    , label
    , lambda
    , langle
    , lbrace
    , lbracket
    , lparen
    , pipe
    , rangle
    , rarrow
    , rbrace
    , rbracket
    , rparen
    ) where

import Data.Foldable
import Data.List.NonEmpty        (NonEmpty (..))
import Data.Text                 (Text)
import Data.Text.Prettyprint.Doc (Doc, Pretty, space)
import Dhall.Map                 (Map)
import Dhall.Set                 (Set)
import Dhall.Src                 (Src (..))
import Dhall.Syntax
import Numeric.Natural           (Natural)

import qualified Data.Char
import qualified Data.HashSet
import qualified Data.List
import qualified Data.List.NonEmpty                        as NonEmpty
import qualified Data.Ratio
import qualified Data.Set
import qualified Data.Text                                 as Text
import qualified Data.Text.Prettyprint.Doc                 as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.String   as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as Terminal
import qualified Data.Text.Prettyprint.Doc.Render.Text     as Pretty
import qualified Dhall.Map                                 as Map
import qualified Dhall.Set

{-| Annotation type used to tag elements in a pretty-printed document for
    syntax highlighting purposes
-}
data Ann
  = Keyword     -- ^ Used for syntactic keywords
  | Syntax      -- ^ Syntax punctuation such as commas, parenthesis, and braces
  | Label       -- ^ Record labels
  | Literal     -- ^ Literals such as integers and strings
  | Builtin     -- ^ Builtin types and values
  | Operator    -- ^ Operators
  deriving Show

{-| Convert annotations to their corresponding color for syntax highlighting
    purposes
-}
annToAnsiStyle :: Ann -> Terminal.AnsiStyle
annToAnsiStyle Keyword  = Terminal.bold <> Terminal.colorDull Terminal.Green
annToAnsiStyle Syntax   = Terminal.bold <> Terminal.colorDull Terminal.Green
annToAnsiStyle Label    = mempty
annToAnsiStyle Literal  = Terminal.colorDull Terminal.Magenta
annToAnsiStyle Builtin  = Terminal.underlined
annToAnsiStyle Operator = Terminal.bold <> Terminal.colorDull Terminal.Green

-- | This type determines whether to render code as `ASCII` or `Unicode`
data CharacterSet = ASCII | Unicode deriving Show

-- | Pretty print an expression
prettyExpr :: Pretty a => Expr s a -> Doc Ann
prettyExpr = prettySrcExpr . denote

prettySrcExpr :: Pretty a => Expr Src a -> Doc Ann
prettySrcExpr = prettyCharacterSet Unicode

{-| Internal utility for pretty-printing, used when generating element lists
    to supply to `enclose` or `enclose'`.  This utility indicates that the
    compact represent is the same as the multi-line representation for each
    element
-}
duplicate :: a -> (a, a)
duplicate x = (x, x)

isWhitespace :: Char -> Bool
isWhitespace c =
    case c of
        ' '  -> True
        '\n' -> True
        '\t' -> True
        '\r' -> True
        _    -> False

{-| Used to render inline `Src` spans preserved by the syntax tree

    >>> let unusedSourcePos = Text.Megaparsec.SourcePos "" (Text.Megaparsec.mkPos 1) (Text.Megaparsec.mkPos 1)
    >>> let nonEmptySrc = Src unusedSourcePos unusedSourcePos "-- Documentation for x\n"
    >>> "let" <> " " <> renderSrc id (Just nonEmptySrc) <> "x = 1 in x"
    let -- Documentation for x
        x = 1 in x
    >>> let emptySrc = Src unusedSourcePos unusedSourcePos "      "
    >>> "let" <> " " <> renderSrc id (Just emptySrc) <> "x = 1 in x"
    let x = 1 in x
    >>> "let" <> " " <> renderSrc id Nothing <> "x = 1 in x"
    let x = 1 in x
-}
renderSrc
    :: (Text -> Text)
    -- ^ Used to preprocess the comment string (e.g. to strip whitespace)
    -> Maybe Src
    -- ^ Source span to render (if present)
    -> Doc Ann
renderSrc strip (Just (Src {..}))
    | not (Text.all isWhitespace srcText) =
        Pretty.align (Pretty.concatWith f newLines <> suffix)
  where
    horizontalSpace c = c == ' ' || c == '\t'

    strippedText = strip srcText

    suffix =
        if Text.null strippedText || Text.last strippedText == '\n'
        then mempty
        else " "

    oldLines = Text.splitOn "\n" strippedText

    spacePrefix = Text.takeWhile horizontalSpace

    commonPrefix a b = case Text.commonPrefixes a b of
        Nothing        -> ""
        Just (c, _, _) -> c

    sharedSpacePrefix []       = ""
    sharedSpacePrefix (l : ls) = foldl' commonPrefix (spacePrefix l) ls

    blank = Text.all horizontalSpace

    newLines =
        case oldLines of
            [] ->
               []
            l0 : ls ->
                let sharedPrefix =
                        sharedSpacePrefix (filter (not . blank) ls)

                    perLine l =
                        case Text.stripPrefix sharedPrefix l of
                            Nothing -> Pretty.pretty l
                            Just l' -> Pretty.pretty l'

                in  Pretty.pretty l0 : map perLine ls

    f x y = x <> Pretty.hardline <> y
renderSrc _ _ =
    mempty

-- Annotation helpers
keyword, syntax, label, literal, builtin, operator :: Doc Ann -> Doc Ann
keyword  = Pretty.annotate Keyword
syntax   = Pretty.annotate Syntax
label    = Pretty.annotate Label
literal  = Pretty.annotate Literal
builtin  = Pretty.annotate Builtin
operator = Pretty.annotate Operator

comma, lbracket, rbracket, langle, rangle, lbrace, rbrace, lparen, rparen, pipe, dollar, colon, equals, dot :: Doc Ann
comma    = syntax Pretty.comma
lbracket = syntax Pretty.lbracket
rbracket = syntax Pretty.rbracket
langle   = syntax Pretty.langle
rangle   = syntax Pretty.rangle
lbrace   = syntax Pretty.lbrace
rbrace   = syntax Pretty.rbrace
lparen   = syntax Pretty.lparen
rparen   = syntax Pretty.rparen
pipe     = syntax Pretty.pipe
dollar   = syntax "$"
colon    = syntax ":"
equals   = syntax "="
dot      = syntax "."

lambda :: CharacterSet -> Doc Ann
lambda Unicode = syntax "??"
lambda ASCII   = syntax "\\"

forall :: CharacterSet -> Doc Ann
forall Unicode = syntax "???"
forall ASCII   = syntax "forall "

rarrow :: CharacterSet -> Doc Ann
rarrow Unicode = syntax "???"
rarrow ASCII   = syntax "->"

doubleColon :: Doc Ann
doubleColon = syntax "::"

-- | Pretty-print a list
list :: [Doc Ann] -> Doc Ann
list   [] = lbracket <> rbracket
list docs =
    enclose
        (lbracket <> space)
        (lbracket <> space)
        (comma <> space)
        (comma <> space)
        (space <> rbracket)
        rbracket
        (fmap duplicate docs)

-- | Pretty-print union types and literals
angles :: [(Doc Ann, Doc Ann)] -> Doc Ann
angles   [] = langle <> rangle
angles docs =
    enclose
        (langle <> space)
        (langle <> space)
        (space <> pipe <> space)
        (pipe <> space)
        (space <> rangle)
        rangle
        docs

-- | Pretty-print record types and literals
braces :: [(Doc Ann, Doc Ann)] -> Doc Ann
braces   [] = lbrace <> rbrace
braces docs =
    enclose
        (lbrace <> space)
        (lbrace <> space)
        (comma <> space)
        (comma <> space)
        (space <> rbrace)
        rbrace
        docs

hangingBraces :: Int -> [(Doc Ann, Doc Ann)] -> Doc Ann
hangingBraces _ [] =
    lbrace <> rbrace
hangingBraces n docs =
    Pretty.group
        (Pretty.flatAlt
            (  lbrace
            <> Pretty.hardline
            <> Pretty.indent n
               ( mconcat (map (combineLong separator) docsLong)
               <> rbrace
               )
            )
            (mconcat (zipWith (<>) (beginShort : repeat separator) docsShort) <> space <> rbrace)
        )
  where
    separator = comma <> space

    docsShort = fmap fst docs

    docsLong = fmap snd docs

    beginShort = lbrace <> space

    combineLong x y = x <> y <> Pretty.hardline

unsnoc :: [a] -> Maybe ([a], a)
unsnoc       []   = Nothing
unsnoc (x0 : xs0) = Just (go id x0 xs0)
  where
    go diffXs x      []  = (diffXs [], x)
    go diffXs x (y : ys) = go (diffXs . (x:)) y ys

-- | Pretty-print anonymous functions and function types
arrows :: CharacterSet -> [ Doc Ann ] -> Doc Ann
arrows characterSet docs = Pretty.group (Pretty.flatAlt long short)
  where
    long = Pretty.align (mconcat (Data.List.intersperse Pretty.hardline docs'))
      where
        docs' = case unsnoc docs of
            Nothing -> docs

            Just (init_, last_) -> init' ++ [ last' ]
              where
                 appendArrow doc = doc <> space <> rarrow characterSet

                 init' = map appendArrow init_

                 last' = space <> space <> last_

    short = mconcat (Data.List.intersperse separator docs)
      where
        separator = space <> rarrow characterSet <> space

combine :: CharacterSet -> Text
combine ASCII   = "/\\"
combine Unicode = "???"

combineTypes :: CharacterSet -> Text
combineTypes ASCII   = "//\\\\"
combineTypes Unicode = "???"

prefer :: CharacterSet -> Text
prefer ASCII   = "//"
prefer Unicode = "???"

equivalent :: CharacterSet -> Text
equivalent ASCII   = "==="
equivalent Unicode = "???"

{-| Format an expression that holds a variable number of elements, such as a
    list, record, or union
-}
enclose
    :: Doc ann
    -- ^ Beginning document for compact representation
    -> Doc ann
    -- ^ Beginning document for multi-line representation
    -> Doc ann
    -- ^ Separator for compact representation
    -> Doc ann
    -- ^ Separator for multi-line representation
    -> Doc ann
    -- ^ Ending document for compact representation
    -> Doc ann
    -- ^ Ending document for multi-line representation
    -> [(Doc ann, Doc ann)]
    -- ^ Elements to format, each of which is a pair: @(compact, multi-line)@
    -> Doc ann
enclose beginShort _         _        _       endShort _       []   =
    beginShort <> endShort
enclose beginShort beginLong sepShort sepLong endShort endLong docs =
    Pretty.group
        (Pretty.flatAlt
            (Pretty.align
                (mconcat (zipWith combineLong (beginLong : repeat sepLong) docsLong) <> endLong)
            )
            (mconcat (zipWith combineShort (beginShort : repeat sepShort) docsShort) <> endShort)
        )
  where
    docsShort = fmap fst docs

    docsLong = fmap snd docs

    combineLong x y = x <> y <> Pretty.hardline

    combineShort x y = x <> y

{-| Format an expression that holds a variable number of elements without a
    trailing document such as nested `let`, nested lambdas, or nested `forall`s
-}
enclose'
    :: Doc ann
    -- ^ Beginning document for compact representation
    -> Doc ann
    -- ^ Beginning document for multi-line representation
    -> Doc ann
    -- ^ Separator for compact representation
    -> Doc ann
    -- ^ Separator for multi-line representation
    -> [(Doc ann, Doc ann)]
    -- ^ Elements to format, each of which is a pair: @(compact, multi-line)@
    -> Doc ann
enclose' beginShort beginLong sepShort sepLong docs =
    Pretty.group (Pretty.flatAlt long short)
  where
    longLines = zipWith (<>) (beginLong : repeat sepLong) docsLong

    long =
        Pretty.align (mconcat (Data.List.intersperse Pretty.hardline longLines))

    short = mconcat (zipWith (<>) (beginShort : repeat sepShort) docsShort)

    docsShort = fmap fst docs

    docsLong = fmap snd docs

alpha :: Char -> Bool
alpha c = ('\x41' <= c && c <= '\x5A') || ('\x61' <= c && c <= '\x7A')

digit :: Char -> Bool
digit c = '\x30' <= c && c <= '\x39'

alphaNum :: Char -> Bool
alphaNum c = alpha c || digit c

headCharacter :: Char -> Bool
headCharacter c = alpha c || c == '_'

tailCharacter :: Char -> Bool
tailCharacter c = alphaNum c || c == '_' || c == '-' || c == '/'

-- | Escape a label if it is not valid when unquoted
escapeLabel :: Bool -> Text -> Text
escapeLabel allowReserved l =
    case Text.uncons l of
        Just (h, t)
            | headCharacter h && Text.all tailCharacter t && (notReservedIdentifier || (allowReserved && someOrNotLanguageKeyword))
                -> l
        _       -> "`" <> l <> "`"
    where
        notReservedIdentifier = not (Data.HashSet.member l reservedIdentifiers)
        someOrNotLanguageKeyword = l == "Some" || not (Data.HashSet.member l reservedKeywords)

prettyLabelShared :: Bool -> Text -> Doc Ann
prettyLabelShared b l = label (Pretty.pretty (escapeLabel b l))

prettyLabel :: Text -> Doc Ann
prettyLabel = prettyLabelShared False

prettyAnyLabel :: Text -> Doc Ann
prettyAnyLabel = prettyLabelShared True

prettyAnyLabels :: Foldable list => list Text -> Doc Ann
prettyAnyLabels =
    mconcat . Pretty.punctuate dot . fmap prettyAnyLabel . toList

prettyLabels :: Set Text -> Doc Ann
prettyLabels a
    | Data.Set.null (Dhall.Set.toSet a) =
        lbrace <> rbrace
    | otherwise =
        braces (map (duplicate . prettyAnyLabel) (Dhall.Set.toList a))

prettyNumber :: Integer -> Doc Ann
prettyNumber = literal . Pretty.pretty

prettyInt :: Int -> Doc Ann
prettyInt = literal . Pretty.pretty

prettyNonZero :: NonZero -> Doc Ann
prettyNonZero = literal . Pretty.pretty

prettyDateTime :: DateTime -> Doc Ann
prettyDateTime = literal . Pretty.pretty

prettyRegex :: Regex -> Doc Ann
prettyRegex = literal . Pretty.pretty

prettyRational :: Rational -> Doc Ann
prettyRational r = (if Data.Ratio.numerator r >= 0 then "+" else "") <> literal (Pretty.pretty (Data.Ratio.numerator r) <> " % !" <> Pretty.pretty (Data.Ratio.denominator r))

prettyNatural :: Natural -> Doc Ann
prettyNatural = literal . Pretty.pretty

prettyDouble :: Double -> Doc Ann
prettyDouble = literal . Pretty.pretty

prettyConst :: Const -> Doc Ann
prettyConst Type = builtin "Type"
prettyConst Kind = builtin "Kind"
prettyConst Sort = builtin "Sort"

prettyVar :: Var -> Doc Ann
prettyVar (V x 0) = label (Pretty.unAnnotate (prettyLabel x))
prettyVar (V x n) = label (Pretty.unAnnotate (prettyLabel x <> "@" <> prettyInt n))

prettyEnvironmentVariable :: Text -> Doc ann
prettyEnvironmentVariable t = Pretty.pretty (escapeEnvironmentVariable t)

preserveSource :: Expr Src a -> Maybe (Doc Ann)
preserveSource (Note Src{..} (DoubleLit  {})) = Just (Pretty.pretty srcText)
preserveSource (Note Src{..} (IntegerLit {})) = Just (Pretty.pretty srcText)
preserveSource (Note Src{..} (NaturalLit {})) = Just (Pretty.pretty srcText)
preserveSource  _                             = Nothing

-- | Escape an environment variable if not a valid Bash environment variable
escapeEnvironmentVariable :: Text -> Text
escapeEnvironmentVariable t
  | validBashEnvVar t = t
  | otherwise         = "\"" <> escapeText_ t <> "\""
  where
    validBashEnvVar v = case Text.uncons v of
        Nothing      -> False
        Just (c, v') ->
                (alpha c || c == '_')
            &&  Text.all (\c' -> alphaNum c' || c' == '_') v'

{-  There is a close correspondence between the pretty-printers in 'prettyCharacterSet'
    and the sub-parsers in 'Dhall.Parser.Expression.parsers'.  Most pretty-printers are
    named after the corresponding parser and the relationship between pretty-printers
    exactly matches the relationship between parsers.  This leads to the nice emergent
    property of automatically getting all the parentheses and precedences right.

    This approach has one major disadvantage: you can get an infinite loop if
    you add a new constructor to the syntax tree without adding a matching
    case the corresponding builder.
-}

{-| Pretty-print an 'Expr' using the given 'CharacterSet'.

'prettyCharacterSet' largely ignores 'Note's. 'Note's do however matter for
the layout of let-blocks:

>>> let inner = Let (Binding Nothing "x" Nothing Nothing Nothing (NaturalLit 1)) (Var (V "x" 0)) :: Expr Src ()
>>> prettyCharacterSet ASCII (Let (Binding Nothing "y" Nothing Nothing Nothing (NaturalLit 2)) inner)
let y = 2 let x = 1 in x
>>> prettyCharacterSet ASCII (Let (Binding Nothing "y" Nothing Nothing Nothing (NaturalLit 2)) (Note (Src unusedSourcePos unusedSourcePos "") inner))
let y = 2 in let x = 1 in x

This means the structure of parsed let-blocks is preserved.
-}
prettyCharacterSet :: Pretty a => CharacterSet -> Expr Src a -> Doc Ann
prettyCharacterSet characterSet expression =
    Pretty.group (prettyExpression expression)
  where
    prettyExpression a0@(Lam _ _ _) =
        arrows characterSet (docs a0)
      where
        docs (Lam a b c) = Pretty.group (Pretty.flatAlt long short) : docs c
          where
            long =  (lambda characterSet <> space)
                <>  Pretty.align
                    (   (lparen <> space)
                    <>  prettyLabel a
                    <>  Pretty.hardline
                    <>  (colon <> space)
                    <>  prettyExpression b
                    <>  Pretty.hardline
                    <>  rparen
                    )

            short = (lambda characterSet <> lparen)
                <>  prettyLabel a
                <>  (space <> colon <> space)
                <>  prettyExpression b
                <>  rparen
        docs c
            | Just doc <- preserveSource c =
                [ doc ]
            | Note _ d <- c =
                docs d
            | otherwise =
                [ prettyExpression c ]
    prettyExpression a0@(BoolIf _ _ _) =
        Pretty.group (Pretty.flatAlt long short)
      where
        prefixesLong =
                ""
            :   cycle
                    [ keyword "then" <> "  "
                    , keyword "else" <> "  "
                    ]

        prefixesShort =
                ""
            :   cycle
                    [ space <> keyword "then" <> space
                    , space <> keyword "else" <> space
                    ]

        longLines = zipWith (<>) prefixesLong (docsLong True a0)

        long =
            Pretty.align (mconcat (Data.List.intersperse Pretty.hardline longLines))

        short = mconcat (zipWith (<>) prefixesShort (docsShort a0))

        docsLong initial (BoolIf a b c) =
            docLong ++ docsLong False c
          where
            padding
                | initial   = "   "
                | otherwise = mempty

            docLong =
                [   keyword "if" <> padding <> " " <> prettyExpression a
                ,   prettyExpression b
                ]
        docsLong initial c
            | Just doc <- preserveSource c =
                [ doc ]
            | Note _ d <- c =
                docsLong initial d
            | otherwise =
                [ prettyExpression c ]

        docsShort (BoolIf a b c) =
            docShort ++ docsShort c
          where
            docShort =
                [   keyword "if" <> " " <> prettyExpression a
                ,   prettyExpression b
                ]
        docsShort c
            | Just doc <- preserveSource c =
                [ doc ]
            | Note _ d <- c =
                docsShort d
            | otherwise =
                [ prettyExpression c ]
    prettyExpression (Let a0 b0) =
        enclose' "" "" space Pretty.hardline
            (fmap (duplicate . docA) (toList as) ++ [ docB ])
      where
        MultiLet as b = multiLet a0 b0

        stripSpaces = Text.dropAround (\c -> c == ' ' || c == '\t')

        -- Strip a single newline character. Needed to ensure idempotency in
        -- cases where we add hard line breaks.
        stripNewline t =
            case Text.uncons t' of
                Just ('\n', t'') -> stripSpaces t''
                _ -> t'
          where t' = stripSpaces t

        docA (Binding src0 c src1 Nothing src2 e) =
            Pretty.group (Pretty.flatAlt long short)
          where
            long =  keyword "let" <> space
                <>  Pretty.align
                    (   renderSrc stripSpaces src0
                    <>  prettyLabel c <> space <> renderSrc stripSpaces src1
                    <>  equals <> Pretty.hardline <> renderSrc stripNewline src2
                    <>  "  " <> prettyExpression e
                    )

            short = keyword "let" <> space <> renderSrc stripSpaces src0
                <>  prettyLabel c <> space <> renderSrc stripSpaces src1
                <>  equals <> space <> renderSrc stripSpaces src2
                <>  prettyExpression e
        docA (Binding src0 c src1 (Just (src3, d)) src2 e) =
                keyword "let" <> space
            <>  Pretty.align
                (   renderSrc stripSpaces src0
                <>  prettyLabel c <> Pretty.hardline <> renderSrc stripNewline src1
                <>  colon <> space <> renderSrc stripSpaces src3 <> prettyExpression d <> Pretty.hardline
                <>  equals <> space <> renderSrc stripSpaces src2
                <>  prettyExpression e
                )

        docB =
            ( keyword "in" <> " " <> prettyExpression b
            , keyword "in" <> "  "  <> prettyExpression b
            )
    prettyExpression a0@(Pi _ _ _) =
        arrows characterSet (docs a0)
      where
        docs (Pi "_" b c) = prettyOperatorExpression b : docs c
        docs (Pi a   b c) = Pretty.group (Pretty.flatAlt long short) : docs c
          where
            long =  forall characterSet <> space
                <>  Pretty.align
                    (   lparen <> space
                    <>  prettyLabel a
                    <>  Pretty.hardline
                    <>  colon <> space
                    <>  prettyExpression b
                    <>  Pretty.hardline
                    <>  rparen
                    )

            short = forall characterSet <> lparen
                <>  prettyLabel a
                <>  space <> colon <> space
                <>  prettyExpression b
                <>  rparen
        docs c
            | Just doc <- preserveSource c =
                [ doc ]
            | Note _ d <- c =
                docs d
            | otherwise =
                [ prettyExpression c ]
    prettyExpression (With a b c) =
            prettyExpression a
        <>  Pretty.flatAlt long short
      where
        short = " " <> keyword "with" <> " " <> update

        long =  Pretty.hardline
            <>  "  "
            <>  Pretty.align (keyword "with" <> " " <> update)

        (update, _) =
            prettyKeyValue prettyAnyLabels prettyOperatorExpression equals (b, c)
    prettyExpression (Assert a) =
        Pretty.group (Pretty.flatAlt long short)
      where
        short = keyword "assert" <> " " <> colon <> " " <> prettyExpression a

        long =
            Pretty.align
            (  "  " <> keyword "assert"
            <> Pretty.hardline <> colon <> " " <> prettyExpression a
            )
    prettyExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyExpression b
        | otherwise =
            prettyAnnotatedExpression a

    prettyAnnotatedExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyAnnotatedExpression (Merge a b (Just c)) =
        Pretty.group (Pretty.flatAlt long short)
      where
        long =
            Pretty.align
                (   keyword "merge"
                <>  Pretty.hardline
                <>  Pretty.indent 2 (prettyImportExpression a)
                <>  Pretty.hardline
                <>  Pretty.indent 2 (prettyImportExpression b)
                <>  Pretty.hardline
                <>  colon <> space
                <>  prettyApplicationExpression c
                )

        short = keyword "merge" <> space
            <>  prettyImportExpression a
            <>  " "
            <>  prettyImportExpression b
            <>  space <> colon <> space
            <>  prettyApplicationExpression c
    prettyAnnotatedExpression (ToMap a (Just b)) =
        Pretty.group (Pretty.flatAlt long short)
      where
        long =
            Pretty.align
                (   keyword "toMap"
                <>  Pretty.hardline
                <>  Pretty.indent 2 (prettyImportExpression a)
                <>  Pretty.hardline
                <>  colon <> space
                <>  prettyApplicationExpression b
                )

        short = keyword "toMap" <> space
            <>  prettyImportExpression a
            <>  space <> colon <> space
            <>  prettyApplicationExpression b
    prettyAnnotatedExpression a0@(Annot _ _) =
        enclose'
            ""
            "  "
            (" " <> colon <> " ")
            (colon <> space)
            (fmap duplicate (docs a0))
      where
        docs (Annot a b) = prettyOperatorExpression a : docs b
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyExpression a ]
    prettyAnnotatedExpression (ListLit (Just a) b) =
            list (map prettyExpression (Data.Foldable.toList b))
        <>  " : "
        <>  prettyApplicationExpression a
-- todo: Nothing case makes no sense!!!!
    prettyAnnotatedExpression (ListFixedLit b c) =
            "~" <> list (map prettyExpression (b:Data.Foldable.toList c))
    prettyAnnotatedExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyAnnotatedExpression b
        | otherwise =
            prettyOperatorExpression a

    prettyOperatorExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyOperatorExpression = prettyEquivalentExpression

    prettyOperator :: Text -> [Doc Ann] -> Doc Ann
    prettyOperator op docs =
        enclose'
            ""
            prefix
            (" " <> operator (Pretty.pretty op) <> " ")
            (operator (Pretty.pretty op) <> spacer)
            (reverse (fmap duplicate docs))
      where
        prefix = if Text.length op == 1 then "  " else "    "

        spacer = if Text.length op == 1 then " "  else "  "

    prettyEquivalentExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyEquivalentExpression a0@(Equivalent _ _) =
        prettyOperator (equivalent characterSet) (docs a0)
      where
        docs (Equivalent a b) = prettyImportAltExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyImportAltExpression a ]
    prettyEquivalentExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyEquivalentExpression b
        | otherwise =
            prettyImportAltExpression a

    prettyImportAltExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyImportAltExpression a0@(ImportAlt _ _) =
        prettyOperator "?" (docs a0)
      where
        docs (ImportAlt a b) = prettyOrExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyOrExpression a ]
    prettyImportAltExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyImportAltExpression b
        | otherwise =
            prettyOrExpression a

    prettyOrExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyOrExpression a0@(BoolOr _ _) =
        prettyOperator "||" (docs a0)
      where
        docs (BoolOr a b) = prettyPlusExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyPlusExpression a ]
    prettyOrExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyOrExpression b
        | otherwise =
            prettyPlusExpression a

    prettyPlusExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyPlusExpression a0@(NaturalPlus _ _) =
        prettyOperator "+" (docs a0)
      where
        docs (NaturalPlus a b) = prettyPercentExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyPercentExpression a ]
    prettyPlusExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyPlusExpression b
        | otherwise =
            prettyPercentExpression a
    prettyPercentExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyPercentExpression a0@(RationalPercent _ _) =
        prettyOperator "%" (docs a0)
      where
        docs (RationalPercent a b) = prettyTextAppendExpression b : docs a
        docs (Note        _ b) = docs b
        docs                b  = [ prettyTextAppendExpression b ]

    prettyPercentExpression (Note _ a) =
        prettyPercentExpression a
    prettyPercentExpression a0 =
        prettyTextAppendExpression a0

    prettyTextAppendExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyTextAppendExpression a0@(TextAppend _ _) =
        prettyOperator "++" (docs a0)
      where
        docs (TextAppend a b) = prettyListAppendExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyListAppendExpression a ]
    prettyTextAppendExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyTextAppendExpression b
        | otherwise =
            prettyListAppendExpression a

    prettyListAppendExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyListAppendExpression a0@(ListAppend _ _) =
        prettyOperator "#" (docs a0)
      where
        docs (ListAppend a b) = prettyAndExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyAndExpression a ]
    prettyListAppendExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyListAppendExpression b
        | otherwise =
            prettyAndExpression a

    prettyAndExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyAndExpression a0@(BoolAnd _ _) =
        prettyOperator "&&" (docs a0)
      where
        docs (BoolAnd a b) = prettyCombineExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyCombineExpression a ]
    prettyAndExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyAndExpression b
        | otherwise =
            prettyCombineExpression a

    prettyCombineExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyCombineExpression a0@(Combine _ _ _) =
        prettyOperator (combine characterSet) (docs a0)
      where
        docs (Combine _ a b) = prettyPreferExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyPreferExpression a ]
    prettyCombineExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyCombineExpression b
        | otherwise =
            prettyPreferExpression a

    prettyPreferExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyPreferExpression a0@(Prefer {}) =
        prettyOperator (prefer characterSet) (docs a0)
      where
        docs (Prefer _ a b) = prettyCombineTypesExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyCombineTypesExpression a ]
    prettyPreferExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyPreferExpression b
        | otherwise =
            prettyCombineTypesExpression a

    prettyCombineTypesExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyCombineTypesExpression a0@(CombineTypes _ _) =
        prettyOperator (combineTypes characterSet) (docs a0)
      where
        docs (CombineTypes a b) = prettyTimesExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyTimesExpression a ]
    prettyCombineTypesExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyCombineTypesExpression b
        | otherwise =
            prettyTimesExpression a

    prettyTimesExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyTimesExpression a0@(NaturalTimes _ _) =
        prettyOperator "*" (docs a0)
      where
        docs (NaturalTimes a b) = prettyEqualExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyEqualExpression a ]
    prettyTimesExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyTimesExpression b
        | otherwise =
            prettyEqualExpression a

    prettyEqualExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyEqualExpression a0@(BoolEQ _ _) =
        prettyOperator "==" (docs a0)
      where
        docs (BoolEQ a b) = prettyNotEqualExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyNotEqualExpression a ]
    prettyEqualExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyEqualExpression b
        | otherwise =
            prettyNotEqualExpression a

    prettyNotEqualExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyNotEqualExpression a0@(BoolNE _ _) =
        prettyOperator "!=" (docs a0)
      where
        docs (BoolNE a b) = prettyApplicationExpression b : docs a
        docs a
            | Just doc <- preserveSource a =
                [ doc ]
            | Note _ b <- a =
                docs b
            | otherwise =
                [ prettyApplicationExpression a ]
    prettyNotEqualExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyNotEqualExpression b
        | otherwise =
            prettyApplicationExpression a

    prettyApplicationExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyApplicationExpression = go []
      where
        go args = \case
            App a b           -> go (b : args) a
            Some a            -> app (builtin "Some") (a : args)
            Merge a b Nothing -> app (keyword "merge") (a : b : args)
            ToMap a Nothing   -> app (keyword "toMap") (a : args)
            e | Note _ b <- e ->
                  go args b
              | null args ->
                  prettyImportExpression e -- just a performance optimization
              | Just doc <- preserveSource e ->
                  app doc args
              | otherwise ->
                  app (prettyImportExpression e) args

        app f args =
            enclose'
                "" "" " " ""
                ( duplicate f
                : map (fmap (Pretty.indent 2) . duplicate . prettyImportExpression) args
                )

    prettyImportExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyImportExpression (Embed a) =
        Pretty.pretty a
    prettyImportExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyImportExpression b
        | otherwise =
            prettyCompletionExpression a

    prettyCompletionExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyCompletionExpression (RecordCompletion a b) =
        case shallowDenote b of
            RecordLit kvs ->
                Pretty.align
                    (   prettySelectorExpression a
                    <>  doubleColon
                    <>  prettyCompletionLit 0 (recordFieldValue <$> kvs)
                    )
            _ ->    prettySelectorExpression a
                <>  doubleColon
                <>  prettySelectorExpression b
    prettyCompletionExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyCompletionExpression b
        | otherwise =
            prettySelectorExpression a

    prettySelectorExpression :: Pretty a => Expr Src a -> Doc Ann
    prettySelectorExpression (Field a b) =
        prettySelectorExpression a <> dot <> prettyAnyLabel b
    prettySelectorExpression (Project a (Left b)) =
        prettySelectorExpression a <> dot <> prettyLabels b
    prettySelectorExpression (Project a (Right b)) =
            prettySelectorExpression a
        <>  dot
        <>  lparen
        <>  prettyExpression b
        <>  rparen
    prettySelectorExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettySelectorExpression b
        | otherwise =
            prettyPrimitiveExpression a

    prettyPrimitiveExpression :: Pretty a => Expr Src a -> Doc Ann
    prettyPrimitiveExpression (Var a) =
        prettyVar a
    prettyPrimitiveExpression (Const k) =
        prettyConst k
    prettyPrimitiveExpression Bool =
        builtin "Bool"

    prettyPrimitiveExpression NonZero =
        builtin "NonZero"
    prettyPrimitiveExpression NonZeroShow =
        builtin "NonZero/show"
    prettyPrimitiveExpression NonZeroClamp =
        builtin "NonZero/clamp"

    prettyPrimitiveExpression NonZeroDiv =
        builtin "NonZero/div"
    prettyPrimitiveExpression NonZeroMod =
        builtin "NonZero/mod"
    prettyPrimitiveExpression NonZeroLog =
        builtin "NonZero/log"
    prettyPrimitiveExpression NonZeroAdd =
        builtin "NonZero/add"
    prettyPrimitiveExpression NonZeroMultiply =
        builtin "NonZero/multiply"
    prettyPrimitiveExpression NonZeroToNatural =
        builtin "NonZero/toNatural"
    prettyPrimitiveExpression NonZeroToInteger =
        builtin "NonZero/toInteger"
    prettyPrimitiveExpression NonZeroParse =
        builtin "NonZero/parse"

    prettyPrimitiveExpression DateTime =
        builtin "DateTime"
    prettyPrimitiveExpression DateTimeShow =
        builtin "DateTime/show"
    prettyPrimitiveExpression DateTimeParse =
        builtin "DateTime/parse"
    prettyPrimitiveExpression DateTimeFromSeconds =
        builtin "DateTime/fromSeconds"
    prettyPrimitiveExpression DateTimeToSeconds =
        builtin "DateTime/toSeconds"

    prettyPrimitiveExpression DateTimeAddYears =
        builtin "DateTime/addYears"
    prettyPrimitiveExpression DateTimeAddMonths =
        builtin "DateTime/addMonths"
    prettyPrimitiveExpression DateTimeAddDays =
        builtin "DateTime/addDays"
    prettyPrimitiveExpression DateTimeFromWeek =
        builtin "DateTime/fromWeek"
    prettyPrimitiveExpression DateTimeToWeek =
        builtin "DateTime/toWeek"
    prettyPrimitiveExpression DateTimeToDate =
        builtin "DateTime/toDate"
    prettyPrimitiveExpression DateTimeFromDate =
        builtin "DateTime/fromDate"
    prettyPrimitiveExpression DateTimeLastDayOfMonth =
        builtin "DateTime/lastDayOfMonth"

    prettyPrimitiveExpression DateTimeGetJulianDay =
        builtin "DateTime/getJulianDay"
    prettyPrimitiveExpression DateTimeSetJulianDay =
        builtin "DateTime/setJulianDay"


    prettyPrimitiveExpression Regex =
        builtin "Regex"
    prettyPrimitiveExpression RegexShow =
        builtin "Regex/show"
    prettyPrimitiveExpression RegexMatch =
        builtin "Regex/match"
    prettyPrimitiveExpression RegexScan =
        builtin "Regex/scan"
    prettyPrimitiveExpression RegexSplit =
        builtin "Regex/split"
    prettyPrimitiveExpression RegexReplace =
        builtin "Regex/replace"
    prettyPrimitiveExpression RegexReplix =
        builtin "Regex/replix"
    prettyPrimitiveExpression RegexParse =
        builtin "Regex/parse"
    prettyPrimitiveExpression RegexToText =
        builtin "Regex/toText"


    prettyPrimitiveExpression Rational =
        builtin "Rational"
    prettyPrimitiveExpression RationalShow =
        builtin "Rational/show"
    prettyPrimitiveExpression RationalFromDouble =
        builtin "Rational/fromDouble"
    prettyPrimitiveExpression RationalToDouble =
        builtin "Rational/toDouble"
    prettyPrimitiveExpression RationalFromRational =
        builtin "Rational/fromRational"
    prettyPrimitiveExpression RationalParse =
        builtin "Rational/parse"

    prettyPrimitiveExpression Natural =
        builtin "Natural"
    prettyPrimitiveExpression NaturalFold =
        builtin "Natural/fold"
    prettyPrimitiveExpression NaturalBuild =
        builtin "Natural/build"
    prettyPrimitiveExpression NaturalIsZero =
        builtin "Natural/isZero"
    prettyPrimitiveExpression NaturalEven =
        builtin "Natural/even"
    prettyPrimitiveExpression NaturalOdd =
        builtin "Natural/odd"
    prettyPrimitiveExpression NaturalToInteger =
        builtin "Natural/toInteger"
    prettyPrimitiveExpression NaturalShow =
        builtin "Natural/show"
    prettyPrimitiveExpression NaturalParse =
        builtin "Natural/parse"
    prettyPrimitiveExpression NaturalToBits =
        builtin "Natural/toBits"
    prettyPrimitiveExpression NaturalSubtract =
        builtin "Natural/subtract"
    prettyPrimitiveExpression NaturalGcd =
        builtin "Natural/gcd"
    prettyPrimitiveExpression Integer =
        builtin "Integer"
    prettyPrimitiveExpression IntegerAdd =
        builtin "Integer/add"
    prettyPrimitiveExpression IntegerMultiply =
        builtin "Integer/multiply"
    prettyPrimitiveExpression IntegerAnd =
        builtin "Integer/and"
    prettyPrimitiveExpression IntegerXor =
        builtin "Integer/xor"
    prettyPrimitiveExpression IntegerClamp =
        builtin "Integer/clamp"
    prettyPrimitiveExpression IntegerNegate =
        builtin "Integer/negate"
    prettyPrimitiveExpression IntegerShow =
        builtin "Integer/show"
    prettyPrimitiveExpression IntegerParse =
        builtin "Integer/parse"
    prettyPrimitiveExpression IntegerToDouble =
        builtin "Integer/toDouble"
    prettyPrimitiveExpression Double =
        builtin "Double"
    prettyPrimitiveExpression DoubleShow =
        builtin "Double/show"
    prettyPrimitiveExpression DoubleParse =
        builtin "Double/parse"
    prettyPrimitiveExpression Text =
        builtin "Text"
    prettyPrimitiveExpression TextShow =
        builtin "Text/show"
    prettyPrimitiveExpression TextToLower =
        builtin "Text/toLower"
    prettyPrimitiveExpression TextToUpper =
        builtin "Text/toUpper"
    prettyPrimitiveExpression TextUnpack =
        builtin "Text/unpack"
    prettyPrimitiveExpression TextPack =
        builtin "Text/pack"
    prettyPrimitiveExpression TextToList =
        builtin "Text/toList"
    prettyPrimitiveExpression TextLength =
        builtin "Text/length"
    prettyPrimitiveExpression TextCompare =
        builtin "Text/compare"
    prettyPrimitiveExpression List =
        builtin "List"
    prettyPrimitiveExpression ListBuild =
        builtin "List/build"
    prettyPrimitiveExpression ListFold =
        builtin "List/fold"
    prettyPrimitiveExpression ListLength =
        builtin "List/length"
    prettyPrimitiveExpression ListHead =
        builtin "List/head"
    prettyPrimitiveExpression ListLast =
        builtin "List/last"
    prettyPrimitiveExpression ListIndexed =
        builtin "List/indexed"
    prettyPrimitiveExpression ListReverse =
        builtin "List/reverse"
    prettyPrimitiveExpression ListPermutations =
        builtin "List/permutations"
    prettyPrimitiveExpression ListChoose =
        builtin "List/choose"
    prettyPrimitiveExpression ListFixed =
        builtin "ListFixed"
    prettyPrimitiveExpression ListFixedFromList =
        builtin "ListFixed/fromList"
    prettyPrimitiveExpression ListFixedToList =
        builtin "ListFixed/toList"
    prettyPrimitiveExpression ListFixedHead =
        builtin "ListFixed/head"
    prettyPrimitiveExpression ListFixedTail =
        builtin "ListFixed/tail"

-- todo
    prettyPrimitiveExpression (Sym t) =
        "^^\"" <> Pretty.pretty t <> "\""
    prettyPrimitiveExpression (SymLit t) =
        "^\"" <> Pretty.pretty t <> "\""
    prettyPrimitiveExpression SymFromText =
        builtin "Sym/fromText"
    prettyPrimitiveExpression SymToText =
        builtin "Sym/toText"

    prettyPrimitiveExpression SZ =
        builtin "SZ"
    prettyPrimitiveExpression SS =
        builtin "SS"
    prettyPrimitiveExpression SZLit =
        "SZLit"
    prettyPrimitiveExpression (SSLit a)
--        "SSLit " <> prettyExpression a

        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyPrimitiveExpression b
        | otherwise =
            Pretty.group (Pretty.flatAlt long short)
      where
        long =
            "SSLit  " <> Pretty.hardline <> -- Pretty.align
                (lparen <> prettyExpression a <> rparen)

        short = "SSLit" <> prettyExpression a



    prettyPrimitiveExpression SSFromNonZero =
        builtin "SS/fromNonZero"
    prettyPrimitiveExpression SSToNonZero =
        builtin "SS/toNonZero"
    prettyPrimitiveExpression SSToNatural =
        builtin "SS/toNatural"
    prettyPrimitiveExpression SSAdd =
        builtin "SS/add"
    prettyPrimitiveExpression SSSubtract =
        builtin "SS/subtract"
    prettyPrimitiveExpression SSEqual =
        builtin "SS/equal"
    prettyPrimitiveExpression SSLessThan =
        builtin "SS/lessThan"

    prettyPrimitiveExpression Proof =
        builtin "Proof"
    prettyPrimitiveExpression ProofLit =
        builtin "Prf"
    prettyPrimitiveExpression ProofToBool =
        builtin "Proof/toBool"
    prettyPrimitiveExpression ProofFromBool =
        builtin "Proof/fromBool"

    prettyPrimitiveExpression PVoid =
        builtin "PVoid"
    prettyPrimitiveExpression PVoidUndefined =
        builtin "PVoid/undefined"
    prettyPrimitiveExpression PVoidError =
        builtin "PVoid/error"
    prettyPrimitiveExpression PVoidKindUndefined =
        builtin "PVoid/kindUndefined"

    prettyPrimitiveExpression Optional =
        builtin "Optional"
    prettyPrimitiveExpression None =
        builtin "None"
    prettyPrimitiveExpression (BoolLit True) =
        builtin "True"
    prettyPrimitiveExpression (BoolLit False) =
        builtin "False"
    prettyPrimitiveExpression (IntegerLit a)
        | 0 <= a    = literal "+" <> prettyNumber a
        | otherwise = prettyNumber a
    prettyPrimitiveExpression (NaturalLit a) =
        prettyNatural a
    prettyPrimitiveExpression (NonZeroLit (NonZeroC a))
        = literal "!" <> prettyNatural a
    prettyPrimitiveExpression (DateTimeLit a) =
        prettyDateTime a
    prettyPrimitiveExpression (RegexLit a) =
        prettyRegex a
    prettyPrimitiveExpression (RationalLit a) =
        prettyRational a
    prettyPrimitiveExpression (DoubleLit (DhallDouble a)) =
        prettyDouble a
    prettyPrimitiveExpression (TextLit a) =
        prettyChunks a
    prettyPrimitiveExpression (Record a) =
        prettyRecord $ recordFieldValue <$> a
    prettyPrimitiveExpression (RecordLit a) =
        prettyRecordLit $ recordFieldValue <$> a
    prettyPrimitiveExpression (Union a) =
        prettyUnion a
    prettyPrimitiveExpression (ListLit Nothing b) =
        list (map prettyExpression (Data.Foldable.toList b))
    prettyPrimitiveExpression (ListFixedLit b c) =
        "~" <> list (map prettyExpression (b:Data.Foldable.toList c))
    prettyPrimitiveExpression a
        | Just doc <- preserveSource a =
            doc
        | Note _ b <- a =
            prettyPrimitiveExpression b
        | otherwise =
            Pretty.group (Pretty.flatAlt long short)
      where
        long =
            Pretty.align
                (lparen <> space <> prettyExpression a <> Pretty.hardline <> rparen)

        short = lparen <> prettyExpression a <> rparen

    prettyKeyValue
        :: Pretty a
        => (k -> Doc Ann)
        -> (Expr Src a -> Doc Ann)
        -> Doc Ann
        -> (k, Expr Src a)
        -> (Doc Ann, Doc Ann)
    prettyKeyValue prettyKey prettyValue separator (key, val) =
        duplicate (Pretty.group (Pretty.flatAlt long short))
      where
        completion _T r =
                " "
            <>  prettySelectorExpression _T
            <>  doubleColon
            <>  case shallowDenote r of
                    RecordLit kvs ->
                        prettyCompletionLit 2 $ recordFieldValue <$> kvs
                    _ ->
                        prettySelectorExpression r

        short = prettyKey key
            <>  " "
            <>  separator
            <>  " "
            <>  prettyValue val

        long =
                prettyKey key
            <>  " "
            <>  separator
            <>  case shallowDenote val of
                    Some val' ->
                            " " <> builtin "Some"
                        <>  case shallowDenote val' of
                                RecordCompletion _T r ->
                                    completion _T r

                                RecordLit _ ->
                                        Pretty.hardline
                                    <>  "  "
                                    <>  prettyImportExpression val'

                                ListLit _ xs
                                    | not (null xs) ->
                                            Pretty.hardline
                                        <>  "  "
                                        <>  prettyImportExpression val'

                                _ ->    Pretty.hardline
                                    <>  "    "
                                    <>  prettyImportExpression val'

                    ToMap val' Nothing ->
                            " " <> keyword "toMap"
                        <>  case shallowDenote val' of
                                RecordCompletion _T r ->
                                    completion _T r
                                _ ->    Pretty.hardline
                                    <>  "    "
                                    <>  prettyImportExpression val'

                    RecordCompletion _T r ->
                        completion _T r

                    RecordLit _ ->
                            Pretty.hardline
                        <>  "  "
                        <>  prettyValue val

                    ListLit _ xs
                        | not (null xs) ->
                                Pretty.hardline
                            <>  "  "
                            <>  prettyValue val

                    _ ->
                            Pretty.hardline
                        <>  "    "
                        <>  prettyValue val

    prettyRecord :: Pretty a => Map Text (Expr Src a) -> Doc Ann
    prettyRecord =
          braces
        . map (prettyKeyValue prettyAnyLabel prettyExpression colon)
        . Map.toList

    prettyRecordLit :: Pretty a => Map Text (Expr Src a) -> Doc Ann
    prettyRecordLit = prettyRecordLike braces

    prettyCompletionLit :: Pretty a => Int -> Map Text (Expr Src a) -> Doc Ann
    prettyCompletionLit = prettyRecordLike . hangingBraces

    prettyRecordLike braceStyle a
        | Data.Foldable.null a =
            lbrace <> equals <> rbrace
        | otherwise =
            braceStyle (map prettyRecordEntry (Map.toList consolidated))
      where
        consolidated = consolidateRecordLiteral a

        prettyRecordEntry (keys, value) =
            case keys of
                key :| []
                    | Var (V key' 0) <- Dhall.Syntax.shallowDenote value
                    , key == key' ->
                        duplicate (prettyAnyLabel key)
                _ ->
                    prettyKeyValue prettyAnyLabels prettyExpression equals (keys, value)

    prettyAlternative (key, Just val) =
        prettyKeyValue prettyAnyLabel prettyExpression colon (key, val)
    prettyAlternative (key, Nothing) =
        duplicate (prettyAnyLabel key)

    prettyUnion :: Pretty a => Map Text (Maybe (Expr Src a)) -> Doc Ann
    prettyUnion =
        angles . map prettyAlternative . Map.toList

    prettyChunks :: Pretty a => Chunks Src a -> Doc Ann
    prettyChunks chunks@(Chunks a b)
        | anyText (== '\n') =
            if not (null a) || anyText (/= '\n')
            then long
            else Pretty.group (Pretty.flatAlt long short)
        | otherwise =
            short
      where
        long =
            Pretty.align
            (   literal "''" <> Pretty.hardline
            <>  Pretty.align
                (foldMap prettyMultilineChunk a' <> prettyMultilineText b')
            <>  literal "''"
            )
          where
            Chunks a' b' = multilineChunks chunks

        short =
            literal "\"" <> foldMap prettyChunk a <> literal (prettyText b <> "\"")

        anyText predicate = any (\(text, _) -> Text.any predicate text) a || Text.any predicate b

        prettyMultilineChunk (c, d) =
                prettyMultilineText c
            <>  dollar
            <>  lbrace
            <>  prettyExpression d
            <>  rbrace

        prettyMultilineText text = mconcat docs
          where
            lines_ = Text.splitOn "\n" (escapeSingleQuotedText text)

            -- Annotate only non-empty lines so trailing whitespace can be
            -- removed on empty ones.
            prettyLine line =
                (if Text.null line then id else literal)
                    (Pretty.pretty line)

            docs =
                Data.List.intersperse Pretty.hardline (map prettyLine lines_)

        prettyChunk (c, d) =
                prettyText c
            <>  syntax "${"
            <>  prettyExpression d
            <>  syntax rbrace

        prettyText t = literal (Pretty.pretty (escapeText_ t))


-- | Prepare 'Chunks' for multi-line formatting by escaping problematic
-- character sequences via string interpolations
--
-- >>> multilineChunks (Chunks [] "\n \tx")
-- Chunks [("\n",TextLit (Chunks [] " \t"))] "x"
-- >>> multilineChunks (Chunks [] "\n\NUL\b\f\t")
-- Chunks [("\n",TextLit (Chunks [] "\NUL\b\f"))] "\t"
multilineChunks :: Chunks s a -> Chunks s a
multilineChunks =
     escapeTrailingSingleQuote
   . escapeControlCharacters
   . escapeSharedWhitespacePrefix

-- | Escape any leading whitespace shared by all lines
--
-- This ensures that significant shared leading whitespace is not stripped
--
-- >>> escapeSharedWhitespacePrefix (Chunks [] "\n \tx")
-- Chunks [("\n",TextLit (Chunks [] " \t"))] "x"
-- >>> escapeSharedWhitespacePrefix (Chunks [("\n",Var (V "x" 0))] " ")
-- Chunks [("\n",Var (V "x" 0))] " "
-- >>> escapeSharedWhitespacePrefix (Chunks [("\n ",Var (V "x" 0))] "")
-- Chunks [("\n",TextLit (Chunks [] " ")),("",Var (V "x" 0))] ""
-- >>> escapeSharedWhitespacePrefix (Chunks [("\n ",Var (V "x" 0))] "\n")
-- Chunks [("\n ",Var (V "x" 0))] "\n"
-- >>> escapeSharedWhitespacePrefix (Chunks [] " ")
-- Chunks [("",TextLit (Chunks [] " "))] ""
escapeSharedWhitespacePrefix :: Chunks s a -> Chunks s a
escapeSharedWhitespacePrefix literal_ = unlinesLiteral literals???
  where
    literals??? = linesLiteral literal_

    sharedPrefix = longestSharedWhitespacePrefix literals???

    stripPrefix = Text.drop (Text.length sharedPrefix)

    escapeSharedPrefix (Chunks [] prefix???)
        | Text.isPrefixOf sharedPrefix prefix??? =
            Chunks [ ("", TextLit (Chunks [] sharedPrefix)) ] prefix???
      where
        prefix??? = stripPrefix prefix???
    escapeSharedPrefix (Chunks ((prefix???, y) : xys) z)
        | Text.isPrefixOf sharedPrefix prefix??? =
            Chunks (("", TextLit (Chunks [] sharedPrefix)) : (prefix???, y) : xys) z
      where
        prefix??? = stripPrefix prefix???
    escapeSharedPrefix line = line

    literals???
        | not (Text.null sharedPrefix) = fmap escapeSharedPrefix literals???
        | otherwise = literals???

-- | Escape control characters by moving them into string interpolations
--
-- >>> escapeControlCharacters (Chunks [] "\n\NUL\b\f\t")
-- Chunks [("\n",TextLit (Chunks [] "\NUL\b\f"))] "\t"
escapeControlCharacters :: Chunks s a -> Chunks s a
escapeControlCharacters (Chunks as0 b0) = Chunks as1 b1
  where
    as1 = foldr f (map toChunk bs) as0

    (bs, b1) = splitOnPredicate predicate b0

    f (t0, e) chunks = map toChunk ts1 ++ (t1, e) : chunks
      where
        (ts1, t1) = splitOnPredicate predicate t0

    predicate c = Data.Char.isControl c && c /= ' ' && c /= '\t' && c /= '\n'

    toChunk (t0, t1) = (t0, TextLit (Chunks [] t1))

-- | Split `Text` on a predicate, preserving all parts of the original string.
--
-- >>> splitOnPredicate (== 'x') ""
-- ([],"")
-- >>> splitOnPredicate (== 'x') " xx "
-- ([(" ","xx")]," ")
-- >>> splitOnPredicate (== 'x') "xx"
-- ([("","xx")],"")
--
-- prop> \(Fun _ p) s -> let {t = Text.pack s; (as, b) = splitOnPredicate p t} in foldMap (uncurry (<>)) as <> b == t
splitOnPredicate :: (Char -> Bool) -> Text -> ([(Text, Text)], Text)
splitOnPredicate p t = case Text.break p t of
    (a, "") -> ([], a)
    (a, b)  -> case Text.span p b of
        (c, d) -> case splitOnPredicate p d of
            (e, f) -> ((a, c) : e, f)

-- | Escape a trailing single quote by moving it into a string interpolation
--
-- Otherwise the multiline-string would end with @'''@, which would be parsed
-- as an escaped @''@.
--
-- >>> escapeTrailingSingleQuote (Chunks [] "\n'")
-- Chunks [("\n",TextLit (Chunks [] "'"))] ""
escapeTrailingSingleQuote :: Chunks s a -> Chunks s a
escapeTrailingSingleQuote chunks@(Chunks as b) =
    case Text.unsnoc b of
        Just (b', '\'') -> Chunks (as ++ [(b', TextLit (Chunks [] "'"))]) ""
        _               -> chunks

-- | Pretty-print a value
pretty_ :: Pretty a => a -> Text
pretty_ = prettyToStrictText

{- This utility function converts
   `{ x = { y = { z = 1 } } }` to `{ x.y.z. = 1 }`
-}
consolidateRecordLiteral
    :: Map Text (Expr s a) -> Map (NonEmpty Text) (Expr s a)
consolidateRecordLiteral = Map.fromList . fmap adapt . Map.toList
  where
    adapt :: (Text, Expr s a) -> (NonEmpty Text, Expr s a)
    adapt (key, expression) =
        case shallowDenote expression of
            RecordLit m ->
                case fmap adapt (Map.toList $ recordFieldValue <$> m) of
                    [ (keys, expression') ] ->
                        (NonEmpty.cons key keys, expression')
                    _ ->
                        (pure key, RecordLit m)
            _ ->
                (pure key, expression)

-- | Escape a `Text` literal using Dhall's escaping rules for single-quoted
--   @Text@
escapeSingleQuotedText :: Text -> Text
escapeSingleQuotedText inputText = outputText
  where
    outputText = substitute "${" "''${" (substitute "''" "'''" inputText)

    substitute before after = Text.intercalate after . Text.splitOn before

{-| Escape a `Text` literal using Dhall's escaping rules

    Note that the result does not include surrounding quotes
-}
escapeText_ :: Text -> Text
escapeText_ text = Text.concatMap adapt text
  where
    adapt c
        | '\x20' <= c && c <= '\x21'     = Text.singleton c
        -- '\x22' == '"'
        | '\x23' == c                    = Text.singleton c
        -- '\x24' == '$'
        | '\x25' <= c && c <= '\x5B'     = Text.singleton c
        -- '\x5C' == '\\'
        | '\x5D' <= c && c <= '\x10FFFF' = Text.singleton c
        | c == '"'                       = "\\\""
        | c == '$'                       = "\\$"
        | c == '\\'                      = "\\\\"
        | c == '\b'                      = "\\b"
        | c == '\f'                      = "\\f"
        | c == '\n'                      = "\\n"
        | c == '\r'                      = "\\r"
        | c == '\t'                      = "\\t"
        | otherwise                      = "\\u" <> showDigits (Data.Char.ord c)

    showDigits r0 = Text.pack (map showDigit [q1, q2, q3, r3])
      where
        (q1, r1) = r0 `quotRem` 4096
        (q2, r2) = r1 `quotRem`  256
        (q3, r3) = r2 `quotRem`   16

    showDigit n
        | n < 10    = Data.Char.chr (Data.Char.ord '0' + n)
        | otherwise = Data.Char.chr (Data.Char.ord 'A' + n - 10)

prettyToString :: Pretty a => a -> String
prettyToString =
    Pretty.renderString . layout . Pretty.pretty

docToStrictText :: Doc ann -> Text.Text
docToStrictText = Pretty.renderStrict . layout

prettyToStrictText :: Pretty a => a -> Text.Text
prettyToStrictText = docToStrictText . Pretty.pretty

-- | Layout using 'layoutOpts'
--
-- Tries hard to fit the document into 80 columns.
--
-- This also removes trailing space characters (@' '@) /unless/
-- they are enclosed in an annotation.
layout :: Pretty.Doc ann -> Pretty.SimpleDocStream ann
layout = Pretty.removeTrailingWhitespace . Pretty.layoutSmart layoutOpts

-- | Default layout options
layoutOpts :: Pretty.LayoutOptions
layoutOpts =
    Pretty.defaultLayoutOptions
        { Pretty.layoutPageWidth = Pretty.AvailablePerLine 80 1.0 }

{- $setup
>>> import Test.QuickCheck (Fun(..))
-}
