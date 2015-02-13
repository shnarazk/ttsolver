{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Timetable
       (
         module SAT.CNFIO
       , Card (..)
       , Quater (..)
       , LQuater (..)
       , DoW (..)
       , Target (..)
       , springSems
       , autumnSems
       , Slot (..)
       , varsForSlot
       , varsForQuater
       , yearOf
       , timeOf
       , dowOf
       , toSlot
       , asSlot
       , succSlot
       , Subject (..)
       , Sub (..)
       , over
       , on
       , canonize
       , renumber
       , defaultRules
       , runSolver
       )
       where
import Control.Applicative
import Control.Monad
import Data.List
import System.Environment
import System.IO
import Text.Printf
import SAT.CNFIO
import qualified SAT.Solver.SIH4 as SAT

-- | 爆発するので1セメスター分しかシミュ−レートしない！
-- 従ってQuaterを表すのには1変数があればよいのだが、、、

-- fundamental types

allItems :: (Bounded a, Enum a) => [a]
allItems = [minBound.. maxBound]

data Card = One | Two | Thr | Fou | Fiv deriving (Bounded, Enum, Eq, Ord, Show)

data Quater = Q1 | Q2 deriving (Bounded, Enum, Eq, Ord, Read, Show)
data  LQuater = Qone | Qtwo deriving (Bounded, Enum, Eq, Ord, Show)

data DoW = Mon | Tue | Wed | Thu | Fri deriving (Bounded, Enum, Eq, Ord, Show)

data Target = B1A | B1B | B2A | B2B | B3A | B3B | B4A
          deriving (Bounded, Enum, Eq, Ord, Read, Show)

springSems = [B1A, B2A, B3A, B4A]
autumnSems = [B1B, B2B, B3B]

data Slot = Mo1 | Mo2 | Mo3 | Mo4 | Mo5
          | Tu1 | Tu2 | Tu3 | Tu4 | Tu5
          | We1 | We2 | We3 | We4 -- We5
          | Th1 | Th2 | Th3 | Th4 | Th5
          | Fr1 | Fr2 | Fr3 | Fr4
          deriving (Bounded, Enum, Eq, Ord, Read, Show)

toLQuater :: Quater -> LQuater  -- used as latex symbol
toLQuater Q1 = Qone
toLQuater Q2 = Qtwo

yearOf :: Subject -> Card
yearOf (target -> y)
  | elem y [B1A, B1B] = One
  | elem y [B2A, B2B] = Two
  | elem y [B3A, B3B] = Thr
  | elem y [B4A] = Fou

timeOf :: Slot -> Card
timeOf s
  | elem s [Mo1, Tu1, We1, Th1, Fr1] = One
  | elem s [Mo2, Tu2, We2, Th2, Fr2] = Two
  | elem s [Mo3, Tu3, We3, Th3, Fr3] = Thr
  | elem s [Mo4, Tu4, We4, Th4, Fr4] = Fou
  | elem s [Mo5, Tu5     , Th5     ] = Fiv

dowOf :: Slot -> DoW
dowOf s
  | elem s [Mo1 .. Mo5] = Mon
  | elem s [Tu1 .. Tu5] = Tue
  | elem s [We1 .. We4] = Wed
  | elem s [Th1 .. Th5] = Thu
  | elem s [Fr1 .. Fr4] = Fri

toSlot :: DoW -> Card -> Slot
toSlot Mon (fromEnum -> n) = [Mo1 .. ] !! n
toSlot Tue (fromEnum -> n) = [Tu1 .. ] !! n
toSlot Wed (fromEnum -> n) = [We1 .. ] !! n
toSlot Thu (fromEnum -> n) = [Th1 .. ] !! n
toSlot Fri (fromEnum -> n) = [Fr1 .. ] !! n

succSlot :: Slot -> Maybe Slot
succSlot Mo2 = Nothing
succSlot Mo5 = Nothing
succSlot Tu2 = Nothing
succSlot Tu5 = Nothing
succSlot We2 = Nothing
succSlot We4 = Nothing
succSlot Th2 = Nothing
succSlot Th5 = Nothing
succSlot Fr2 = Nothing
succSlot Fr4 = Nothing
succSlot n = Just . toEnum . (1 +) . fromEnum $ n

data Subject = Subject
               {
                 labelOf :: String -- ^ 科目名
               , target :: Target  -- ^ 春/秋開講時期
               , required :: Bool  -- ^ 必修/選択
               , lecturersOf :: [String] -- ^ 担当教員群
               , isLong :: Maybe Int     -- ^ 連続コマの有無
               , preqsOf :: [String]     -- ^ 履修条件
               , sameWith :: [String]    -- ^ 同時開講科目
               , atComputerRoom :: Bool    -- ^ 演習室使用
               , subjectNumber :: Int
               }
               deriving (Eq, Ord, Show)

--instance Show Subject where
--  show = labelOf

data Sub = Sub String Target Bool [String] (Maybe Int) [String] [String] Bool

canonize :: [Sub] -> [Subject]
canonize = renumber . concatMap unfoldSubject

renumber :: [Subject] -> [Subject]
renumber l = zipWith (\sub nu -> sub { subjectNumber = nu }) l [0 :: Int ..]

unfoldSubject :: Sub -> [Subject]
unfoldSubject sub@(Sub la ta re ls is pr sa at)
  | lc == '\'' = [Subject namep ta re ls is pr sa at 0, Subject nameq ta re ls is pr [namep] at 0]    -- 科目名が'で終わると同時開講
  | lc == '+'  = [Subject name1 ta re ls is pr sa at 0, Subject name2 ta re ls is [name1] sa at 0]    -- 科目名が*で終わると2クォーター開講
  | lc == '?'  = [Subject name  ta re ls is pr sa at 0, Subject (name ++ "?") ta re ls is pr sa at 0] -- 科目名が?で終わると2コマ必要
  | otherwise  = [Subject la ta re ls is pr sa at 0]
    where
      name1 = init la ++ "→"
      name2 = "→" ++ init la
      namep = init la ++ "'"
      nameq = init la ++ "''"
      name = init la
      lc = last la

{-
instance Bounded Subject where
  minBound = head subjects
  maxBound = last subjects

instance Enum Subject where
  succ = toEnum . succ . fromEnum
  pred = toEnum . pred . fromEnum
  toEnum n = subjects !! n
  fromEnum s = length $ takeWhile (/= s) subjects 
-}

bundleSize :: Int
bundleSize = 1 + length (allItems :: [Slot]) -- 1 bit for quater

indexOf :: [Subject] -> Subject -> Int
indexOf l x = loop l 0
  where
    loop [] n = error $ "indexOf: can't find " ++ show x
    loop (y:l) n = if x == y then n else loop l $ n + 1

varsForQuater :: Subject -> (Int, Int)
varsForQuater s = (base + 1, base + 1)
  where
    base = subjectNumber s * bundleSize
   
varsForSlot :: Subject -> (Int, Int)
varsForSlot s = (base + 1, base + length (allItems :: [Slot]))
  where
    base = subjectNumber s * bundleSize + 1

rangeOver :: (Int, Int) -> [Int]
rangeOver (a, b) = [a .. b]

over :: (Subject -> (Int, Int)) -> Subject -> [Int]
over f = rangeOver . f

fromName :: [Subject] -> String -> Subject
fromName subjects l
  | Just x <- find ((l ==) . labelOf) subjects = x
  | otherwise = error ""

on :: Int -> Subject -> Int
on n s = 1 + subjectNumber s * bundleSize + mod (n - 1) bundleSize

interpretationOf :: [Subject] -> Int -> (Subject, String, Bool)
interpretationOf subs x = (sub, kind, 0 < x)
  where
    sub :: Subject
    sub = subs !! div (abs x) bundleSize
    kind :: String
    kind = let pos = mod (abs x - 1) bundleSize
               numQ = 1
           in
            if pos < numQ
            then show ((toEnum pos) :: Quater)
            else show (toEnum (pos - numQ) :: Slot)

interprete :: [Int] -> Subject -> (Quater, Slot)
interprete l s
  | s' == [] = error $ "no assignment to " ++ labelOf s 
  | length s' == 1 = (if [] == q' then Q1 else Q2, head s')
  | otherwise = error $ "strange assignment: " ++ show (labelOf s , (q', s'))
  where
    q' = filter (flip elem qs) l
    s' = map toS $ filter (flip elem ss) l
    qs = varsForQuater `over` s
    ss = varsForSlot `over` s
    toS x = toEnum . subtract numQ $ mod (abs x - 1) bundleSize
    numQ = 1

asQuater :: Int -> Maybe Quater
asQuater (abs -> n)
  | mod (n - 1) bundleSize < 1 = Just (toQ n)
  | otherwise = Nothing
  where
    toQ x = toEnum $ mod (abs x - 1) bundleSize

asSlot :: Int -> Maybe Slot
asSlot (abs -> n)
  | 1 < 1 + mod (n - 1) bundleSize = Just (toS n)
  | otherwise = Nothing
  where
    toS x = toEnum . subtract numQ $ mod (abs x - 1) bundleSize
    numQ = 1

asDOW :: Int -> Maybe Int
asDOW (abs -> n)
  | not (1 < 1 + mod (n - 1) bundleSize) = Nothing
  | elem slot [Mo1 .. Mo5] = Just 1
  | elem slot [Tu1 .. Tu5] = Just 2
  | elem slot [We1 .. We4] = Just 3
  | elem slot [Th1 .. Th5] = Just 4
  | elem slot [Fr1 .. Fr4] = Just 5
  where
    slot = toEnum . subtract numQ $ mod (abs n - 1) bundleSize
    numQ = 1

-- | imcompatible relation

(<!>) :: Subject -> Subject -> BoolForm
s1 <!> s2 = (-&&&-) [ (q -!- (q `on` s2)) -|- neg s -|- neg (s `on` s2)
                    | q <- varsForQuater `over` s1
                    , s <- varsForSlot `over` s1
                    , s1 /= s2  -- for fail-safe
                    ]

--------------------------------------------------------------------------------
-- RULES
--------------------------------------------------------------------------------

-- | 講師は同一時間帯は持てない
cond0 subs fixed = (-&&&-) [ sub' <!> sub
                     | sub <- subs
                     , lecturer <- lecturersOf sub
                     , sub' <- filter (elem lecturer . lecturersOf) subs
                     , sub < sub'
                     ]
              -&-
              (-&&&-) [ neg s    -- 1年科目との整合性
                      | sub <- subs
                      , lect <- lecturersOf sub
                      , ((_, _, dow, num), sub') <- filter (elem lect . lecturersOf . snd) $ fixed
                      , (target sub' == B1A && elem (target sub) springSems) || (target sub' == B1B && elem (target sub) autumnSems) 
                      , s <- varsForSlot `over` sub
                      , asSlot s == Just (toSlot dow num)
                      ]

-- | 第2学年は月火がだめ、第4学年は月がだめ
cond1 subs = (-&&&-) [ neg s
                     | sub <- subs
                     , elem (target sub) [B2A, B2B]
                     , s <- varsForSlot `over` sub
                     , elem (asSlot s) [Just s | s <- [Mo1 .. Tu5]]
                     ]
             -&-
             (-&&&-) [ neg s -&- neg q
                     | sub <- subs
                     , elem (target sub) [B4A]
                     , q <- varsForQuater `over` sub
                     , s <- varsForSlot `over` sub
                     , elem (asSlot s) [Just s | s <- [Mo1 .. Mo5]]
                     ]

-- | 全てのSubjectのslot割当ては1つのみT
cond2 subs = (-&&&-) [ neg s1 -|- neg s2
                     | sub <- subs
                     , s1 <- varsForSlot `over` sub
                     , s2 <- varsForSlot `over` sub
                     , s1 < s2
                     ]
             -&-
             (-&&&-)[ (-|||-) [ toBF s | s <- varsForSlot `over` sub] | sub <- subs ]

-- | 全てのSubjectのQuater割当て値は1つのみT
cond2' subs = (-&&&-) [ neg q1 -|- neg q2
                     | sub <- subs
                     , q1 <- varsForQuater `over` sub
                     , q2 <- varsForQuater `over` sub
                     , q1 < q2
                     ]
             -&-
             (-&&&-) [ (-|||-) [ toBF q | q <- varsForQuater `over` sub] | sub <- subs ]

-- cond2 _ = toBF True

-- | 同学年内では同じ割当てが2回出現することはない
cond3 subs = (-&&&-) [ sub <!> sub'
                     | sub  <- subs
                     , sub' <- subs
                     , target sub == target sub'
                     , sub < sub'
                     ]

-- | nコマの科目は次の連続する(n-1)コマが存在するコマでなければならない
cond4 subs = (-&&&-) [ neg s
                     | sub <- filter ((Nothing /=) . isLong) subs
                     , s <- varsForSlot `over` sub
                     , case isLong sub of
                         Just 2 -> (succSlot =<< asSlot s) == Nothing
                         Just 3 -> (succSlot =<< succSlot =<< asSlot s) == Nothing
                         _ -> False
                     ]

-- | nコマの科目はそれらのコマにも同学年の他の科目が入ってはいけない
cond5 subs = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg (s' `on` sub')
                     | sub <- filter ((Nothing /=) . isLong) subs
                     , q <- varsForQuater `over` sub
                     , s <- varsForSlot `over` sub
                     , sub' <- subs
                     , target sub == target sub'
                     , sub /= sub'
                     , s' <- varsForSlot `over` sub'
                     , (succSlot =<< asSlot s) /= Nothing
                     , case isLong sub of
                         Just 2 -> asSlot s' == (succSlot =<< asSlot s)
                         Just 3 -> asSlot s' == (succSlot =<< asSlot s) || asSlot s' == (succSlot =<< succSlot =<< asSlot s)
                         _ -> False
                     ]

-- | 前件科目のチェック
cond6 subs = (-&&&-) [ neg q' -&- q
                     | sub <- filter (([] /=) . preqsOf) subs
                     , sub' <- map (fromName subs) (preqsOf sub)
                     , q <- varsForQuater `over` sub
                     , q' <- varsForQuater `over` sub'
                     -- , Just True == ((<=) <$> asQuater q <*> asQuater q')
                     ]

-- | 同時開講科目のチェック
cond7 subs = (-&&&-) [ q -=- (q `on` sub')
                     | sub <- filter (([] /=) . sameWith) subs
                     , sub' <- map (fromName subs) (sameWith sub)
                     , sub /= sub'
                     , q <- varsForQuater `over` sub
                     ]

-- | 演習室はひとつしかない
cond8 subs = (-&&&-) [ sub' <!> sub
                     | sub <- filter atComputerRoom subs
                     , sub' <- filter atComputerRoom subs
                     , sub' < sub
                     ]
             -&-                -- nコマ連続科目の処理
             (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg s'
                     | sub <- filter atComputerRoom subs
                     , Nothing /= isLong sub
                     , q <- varsForQuater `over` sub
                     , s <- varsForSlot `over` sub
                     , sub' <- filter atComputerRoom subs
                     , sub' /= sub
                     , s' <- varsForSlot `over` sub'
                     , (succSlot =<< asSlot s) /= Nothing
                     , case isLong sub of
                         Just 2 -> asSlot s' == (succSlot =<< asSlot s)
                         Just 3 -> asSlot s' == (succSlot =<< asSlot s) || asSlot s' == (succSlot =<< succSlot =<< asSlot s)
                         _ -> False
                     ]

-- | 3,4年の講義に関しては講師は1日に2つ講義を持たない
cond9 subs = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg s'
                      | sub <- subs
                      , elem (target sub) [B2A ..]
                      , lecturer <- lecturersOf sub
                      , sub' <- subs
                      , elem (target sub') [B2A ..]
                      , sub < sub'
                      , elem lecturer (lecturersOf sub')
                      , q <- varsForQuater `over` sub
                      , s <- varsForSlot `over` sub
                      , s' <- varsForSlot `over` sub'
                      , asDOW s == asDOW s'
                      ]
{-
              -&- -- 2年の講義間に関しても講師は1日に2つ講義を持たない
              (-&&&-) [ neg q -|- neg (q `on` sub') -|- neg s -|- neg s'
                      | sub <- subs
                      , elem (target sub) [B2A .. B2B]
                      , lecturer <- lecturersOf sub
                      , sub' <- subs
                      , elem (target sub') [B2A .. B2B]
                      , sub < sub'
                      , elem lecturer (lecturersOf sub')
                      , q <- varsForQuater `over` sub
                      , s <- varsForSlot `over` sub
                      , s' <- varsForSlot `over` sub'
                      , asDOW s == asDOW s'
                      ]
-}
{-
-- | 講師は同日に1、2校時または2,3校時のペアを持ってはならない。
              -&-
              (-&&&-) [ neg q -|- neg (q `on` sub') -|- neg s -|- neg s'
                      | sub <- subs
                      , lecturer <- lecturersOf sub
                      , sub' <- subs
                      , sub /= sub'
                      , elem lecturer (lecturersOf sub')
                      , q <- varsForQuater `over` sub
                      , s <- varsForSlot `over` sub
                      , s' <- varsForSlot `over` sub'
                      , elem (asSlot s, asSlot s') [(Just a, Just b) | (a, bs) <- [(Mo2, [Mo1, Mo3]), (Tu2, [Tu1, Tu3]), (We2, [We1, We3]), (Th2, [Th1, Th3]), (Fr2, [Fr1, Fr3]), (Mo4, [Mo5]), (Tu4, [Tu5]), (Th4, [Th5])], b <- bs]
                      ]
-}
--cond10 _ = toBF True

-- | 2年と3年の必修科目は重ねない
cond11' subs = (-&&&-) [ sub <!> sub'
                      | sub <- filter (flip elem [B2A, B2B, B3A, B3B] . target) $ filter required subs
                      , sub' <- filter (flip elem [B2A, B2B, B3A, B3B] . target) $ filter required subs
                      , sub < sub'
                      ]
             -&-                -- nコマ連続科目の処理
             (-&&&-) [ neg q -|- neg (q `on` sub') -|- neg s -|- neg s'
                     | sub <- filter (flip elem [B2A, B2B, B3A, B3B] . target) $ filter required subs
                     , Nothing /= isLong sub
                     , q <- varsForQuater `over` sub
                     , s <- varsForSlot `over` sub
                     , sub' <- filter (flip elem [B2A, B2B, B3A, B3B] . target) $ filter required subs
                     , sub' /= sub
                     , s' <- varsForSlot `over` sub'
                     , (succSlot =<< asSlot s) /= Nothing
                     , case isLong sub of
                         Just 2 -> asSlot s' == (succSlot =<< asSlot s)
                         Just 3 -> asSlot s' == (succSlot =<< asSlot s) || asSlot s' == (succSlot =<< succSlot =<< asSlot s)
                         _ -> False
                     ]
cond11 _ = toBF True

-- | 第3学年Q2に必修はいれない
cond12' subs = (-&&&-) [ neg q
                     | sub <- filter required subs
                     , target sub == B3A
                     , q <- varsForQuater `over` sub
                     -- , s <- varsForSlot `over` sub
                     -- , elem (asQuater q, asSlot s) [(Just Q2, Just s) | s <- allItems]
                     ]
cond12 _ = toBF True

defaultRules = ([cond0], [cond1, cond2, cond3, cond4, cond5, cond6, cond7, cond8, cond9])

checkConsistenry subjects
  | [] /= preqs \\ labels = error $ "`preqs` contains non-existing subject: " ++ show (preqs, labels)
  | [] /= sames \\ labels = error $ "`same` contains non-existing subject: " ++ show (sames, labels)
  | any ([] ==) (map lecturersOf subjects) = error $ "subject without lecturer: " ++ show (filter (([] ==) . lecturersOf) subjects)
  | [] /= out1 = error $ "Q1, Q2科目内で順序が閉じてない: " ++ head out1
  | [] /= out2 = error $ "Q3, Q4科目内で順序が閉じてない: " ++ head out2
  | 23 < length lects = error $ "too many lecturers:" ++ intercalate "," lects
  | otherwise = True
  where
    labels = sort $ map labelOf subjects
    preqs = sort $ nub $ concatMap preqsOf subjects
    sames = sort $ nub $ concatMap sameWith subjects
    subAs = filter (flip elem springSems . target) subjects
    subBs = filter (flip elem autumnSems . target) subjects
    out1 = (nub $ concatMap preqsOf subAs) \\ map labelOf subAs
    out2 = (nub $ concatMap preqsOf subBs) \\ map labelOf subBs
    n = length subjects
    lects = nub $ concatMap lecturersOf subjects

splitBySeason subs = (renumber $ filter ((flip elem springSems) . target) subs, renumber $ filter ((flip elem autumnSems) . target) subs)

runSolver mkrule fixed subjects = do
  let (subjectsInSpring, subjectsInAutomn) = splitBySeason subjects
  os <- getArgs
  unless (checkConsistenry subjectsInSpring) $ error "exit"
  unless (checkConsistenry subjectsInAutomn) $ error "exit"
  let (r1, r2) = (mkrule subjectsInSpring, mkrule subjectsInAutomn)
  let printer subs ans = do
        let x = filter (0 <) . (take (length subs * bundleSize)) $ ans
        let comp (p1, s1) (p2, s2) = case compare (target s1) (target s2) of { EQ -> compare p1 p2; x -> x }
        let l = sortBy comp $ map (\s -> (interprete x s, s)) subs
        let b1l = filter (flip elem [B1A, B1B] . target . snd) l
        let b2l = filter (flip elem [B2A, B2B] . target . snd) l
        let b3l = filter (flip elem [B3A, B3B] . target . snd) l
        let b4l = filter (flip elem [B4A] . target . snd) l
        forM_ [("B1", b1l), ("B2", b2l), ("B3", b3l), ("B4", b4l)] $ \(y, yl) -> do
          putStrLn $ "### " ++ y
          forM_ yl $ \((q, r), s) -> do
            putStr $ printf "%s %s: %-24s" (show q) (show r) (labelOf s)
            putStrLn . ("\t" ++) . intercalate ", " $ lecturersOf s
  let makeTable fixed subs ans = do
        let x = filter (0 <) . (take (length subs * bundleSize)) $ ans
        let comp (p1, s1) (p2, s2) = case compare (target s1) (target s2) of { EQ -> compare p1 p2; x -> x }
        let l = sortBy comp $ map (\s -> (interprete x s, s)) subs
        let table = fixed ++ (flip map l $ \((quater, slot), subject) -> ((yearOf subject, toLQuater quater, dowOf slot, timeOf slot), subject))
        let (h, p) = if subs == subjectsInSpring then ("timetable-spring.tex", "Sp") else ("timetable-automn.tex", "Au")
        -- toLatexTable p table
        withFile h WriteMode $ toLatex p table
  case os of
    ("-i":_) -> do
      printer (if elem "B" os then subjectsInAutomn else subjectsInSpring) . read =<< getContents
    ("-d":_) -> do
      putStrLn . asCNFString $ if elem "B" os then r2 else r1
    _ -> do
      let anss = map (SAT.satisfiable (:) . asList) [r1, r2]
      let fxs = [filter ((B1A ==) . target . snd) fixed, filter ((B1B ==) . target . snd) fixed]
      forM_ (zip3 fxs anss [subjectsInSpring, subjectsInAutomn]) $ \(fixed, res, subs) -> do
        putStr $ "-------- " ++ if subs == subjectsInSpring then "春学期" else "秋学期"
        let (Cnf (n, _) l) = if subs == subjectsInSpring then r1 else r2
        putStrLn $ "; " ++ show (n, length l)
        case res of
          [] -> putStrLn "can't solve"
          (r:_) -> printer subs r >> makeTable fixed subs r

toLatex :: String -> [((Card, LQuater, DoW, Card), Subject)] -> Handle -> IO ()
toLatex p table h = do
  forM_ tags $ \(k@(_, q, _, _), s) -> do
    case find ((k ==) . fst) table of
      Just (_, sub) -> do
        let name = labelOf sub
        let lec = lecturersOf sub
        case (required sub, atComputerRoom sub) of
          (True , True ) -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\cellcolor{blue!10}\\textcolor{red}{\\textbf{%s}}}" p s name
          (True , False) | q == Qone -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\textcolor{red}{\\textbf{%s}}}" p s name
          (True , False) | q == Qtwo -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\cellcolor{black!5}\\textcolor{red}{\\textbf{%s}}}" p s name
          (False, True ) -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\cellcolor{blue!10}%s}" p s name
          (False, False) | q == Qone -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{%s}" p s name
          (False, False) | q == Qtwo -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\cellcolor{black!5}%s}" p s name
        if q == Qone
          then hPutStrLn h $ printf "\\newcommand{\\%s%sLec}{\\footnotesize %s}" p s (head lec)
          else hPutStrLn h $ printf "\\newcommand{\\%s%sLec}{\\cellcolor{black!5}\\footnotesize %s}" p s (head lec)
      _ | q == Qone -> do
        hPutStr h $ printf "\\newcommand{\\%s%sSub}{}" p s
        hPutStrLn h $ printf "\\newcommand{\\%s%sLec}{}" p s
      _ -> do
        hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\cellcolor{black!5}}" p s
        hPutStrLn h $ printf "\\newcommand{\\%s%sLec}{\\cellcolor{black!5}}" p s
  where
    tags = [ ( (y, q, d, s)
             , (printf "%s%s%s%s" (show y) (show q) (show d) (show s)) :: String)
           | y <- [minBound :: Card .. Fou]
           , q <- [minBound :: LQuater .. maxBound]
           , d <- [minBound :: DoW .. maxBound]
           , s <- [minBound :: Card .. Fiv]
           ]

toLatexTable :: String -> [(Subject, (Card, LQuater, DoW, Card), (String, [String]))] -> IO ()
toLatexTable p _ = do
  forM_ [minBound :: DoW .. maxBound] $ \d -> do
    forM_ [minBound :: Card .. Fiv] $ \s -> do
      putStr $ "&" ++ show (fromEnum s + 1) ++ "&"
      forM_ [minBound :: Card .. Fou] $ \y -> do
        forM_ [minBound :: LQuater .. maxBound] $ \q -> do
          putStr ((printf "\\%s%s%s%s%sSub&" p (show y) (show q) (show d) (show s)) :: String)
          putStr ((printf "\\%s%s%s%s%sLec" p (show y) (show q) (show d) (show s)) :: String)
          if q == maxBound && y == Fou then putStrLn "\\\\\\hline" else putStr "&"
