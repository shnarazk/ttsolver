{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Timetable
       (
         module SAT.CNFIO
       , Year (..)
       , Season (..)
       , Quarter (..)
       , DoubleQuarter (..)
       , DoW (..)
       , Hour (..)
       , Target (..)
       , springSems
       , autumnSems
       , Slot (..)
       , varsForSlot
       , varsForDoubleQuarter
       , yearOfSubject
       , hourOf
       , dowOf
       , toSlot
       , as_Slot
       , succSlot
       , Subject (..)
       , Sub (..)
       , TimeTable
       , over
       , on
       , canonize
       , renumber
       , defaultRules
       , runSolver
       , isFixed
       )
       where
import Control.Applicative
import Control.Monad
import Data.List
import Data.Time
import System.Environment
import System.IO
import Text.Printf
import SAT.CNFIO
import qualified SAT.Solver.SIH4 as SAT

-- | 爆発するので1セメスター分しかシミュ−レートしない！
-- 従ってQuarterを表すのには1変数があればよいのだが、、、

-- fundamental types

allItems :: (Bounded a, Enum a) => [a]
allItems = [minBound.. maxBound]

data Year = Y1 | Y2 | Y3 | Y4 deriving (Bounded, Enum, Eq, Ord, Show)
data Season = Spring | Autumn deriving (Bounded, Enum, Eq, Ord, Show)
data Quarter = Q1 | Q2 | Q3 | Q4 deriving (Bounded, Enum, Eq, Ord, Show)
data DoubleQuarter = DQ1 | DQ2 deriving (Bounded, Enum, Eq, Ord, Read, Show)
data DoW = Mon | Tue | Wed | Thu | Fri deriving (Bounded, Enum, Eq, Ord, Show)
data Hour = H1 | H2 | H3 | H4 | H5 deriving (Bounded, Enum, Eq, Ord, Show)

data Target = B1A | B1B | B2A | B2B | B3A | B3B | B4A
          deriving (Bounded, Enum, Eq, Ord, Read, Show)

springSems = [B1A, B2A, B3A, B4A]
autumnSems = [B1B, B2B, B3B]

seasonOfSubject :: Subject -> Season
seasonOfSubject (subjectNumber -> Right e) = seasonOfEntry e
seasonOfSubject (target -> t)
  | elem t springSems = Spring
  | otherwise = Autumn

data Slot = Mo1 | Mo2 | Mo3 | Mo4 | Mo5
          | Tu1 | Tu2 | Tu3 | Tu4 | Tu5
          | We1 | We2 | We3 | We4 -- We5
          | Th1 | Th2 | Th3 | Th4 | Th5
          | Fr1 | Fr2 | Fr3 | Fr4
          deriving (Bounded, Enum, Eq, Ord, Read, Show)

yearOfSubject :: Subject -> Year
yearOfSubject (target -> y)
  | elem y [B1A, B1B] = Y1
  | elem y [B2A, B2B] = Y2
  | elem y [B3A, B3B] = Y3
  | elem y [B4A] = Y4

seasonOf :: Quarter -> Season
seasonOf Q1 = Spring
seasonOf Q2 = Spring
seasonOf Q3 = Autumn
seasonOf Q4 = Autumn

hourOf :: Slot -> Hour
hourOf s
  | elem s [Mo1, Tu1, We1, Th1, Fr1] = H1
  | elem s [Mo2, Tu2, We2, Th2, Fr2] = H2
  | elem s [Mo3, Tu3, We3, Th3, Fr3] = H3
  | elem s [Mo4, Tu4, We4, Th4, Fr4] = H4
  | elem s [Mo5, Tu5     , Th5     ] = H5

dowOf :: Slot -> DoW
dowOf s
  | elem s [Mo1 .. Mo5] = Mon
  | elem s [Tu1 .. Tu5] = Tue
  | elem s [We1 .. We4] = Wed
  | elem s [Th1 .. Th5] = Thu
  | elem s [Fr1 .. Fr4] = Fri

toSlot :: DoW -> Hour -> Slot
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

type Entry = (Year, Quarter, DoW, Hour)

targetOfEntry :: Entry -> Target
targetOfEntry (y, q, _, _)
  | y == Y1 && elem q [Q1, Q2] = B1A
  | y == Y1 && elem q [Q3, Q4] = B1B
  | y == Y2 && elem q [Q1, Q2] = B2A
  | y == Y2 && elem q [Q3, Q4] = B2B
  | y == Y3 && elem q [Q1, Q2] = B3A
  | y == Y3 && elem q [Q3, Q4] = B3B
  | y == Y4 && elem q [Q1, Q2] = B4A
  | y == Y4 && elem q [Q3, Q4] = error "targetOfEntry : out of range"

seasonOfEntry :: Entry -> Season
seasonOfEntry (_, Q1, _, _) = Spring
seasonOfEntry (_, Q2, _, _) = Spring
seasonOfEntry (_, Q3, _, _) = Autumn
seasonOfEntry (_, Q4, _, _) = Autumn

slotOfEntry :: Entry -> Slot
slotOfEntry (_, _, Mon, h) = [Mo1 ..] !! fromEnum h
slotOfEntry (_, _, Tue, h) = [Tu1 ..] !! fromEnum h
slotOfEntry (_, _, Wed, h) = [We1 ..] !! fromEnum h
slotOfEntry (_, _, Thu, h) = [Th1 ..] !! fromEnum h
slotOfEntry (_, _, Fri, h) = [Fr1 ..] !! fromEnum h

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
               , subjectNumber :: Either Int (Entry)
               }
               deriving (Eq, Ord, Show)

isFixed :: Subject -> Bool
isFixed (subjectNumber -> Left _) = False
isFixed (subjectNumber -> Right _) = True

type TimeTable = [(Entry, Subject)]

data Sub
  = Sub    String Target         Bool [String] (Maybe Int) [String] [String] Bool
  | Fixed  String Entry          Bool [String] (Maybe Int) [String] [String] Bool
  | FixedQ String (Year, Quarter) Bool [String] (Maybe Int) [String] [String] Bool

canonize :: [Sub] -> [Subject]
canonize = renumber . concatMap unfoldSubject

renumber :: [Subject] -> [Subject]
renumber l = loop l 1
  where
    loop [] _                         = []
    loop (sub@(isFixed -> True):l)  n = sub                            : loop l n
    loop (sub@(isFixed -> False):l) n = sub { subjectNumber = Left n } : loop l (n + 1)

unfoldSubject :: Sub -> [Subject]
unfoldSubject sub@(Fixed la en re ls is pr sa at) = [Subject la (targetOfEntry en) re ls is pr sa at (Right en)]
unfoldSubject sub@(Sub la ta re ls is pr sa at)
  -- 科目名が'で終わると同時開講
  | lc == '\''  = [Subject namep ta re ls is pr sa at z, Subject nameq ta re ls is pr [namep] at z]
  -- 科目名が*で終わると2クォーター開講
  | lc == '+'   = [Subject name1 ta re ls is pr sa at z, Subject name2 ta re ls is [name1] sa at z]
  -- 科目名が?で終わると2コマ必要
  | lc == '?'   = [Subject name  ta re ls is pr sa at z, Subject (name ++ "?") ta re ls is pr sa at z]
  | otherwise   = [Subject la ta re ls is pr sa at z]
    where
      z = Left 0
      name1 = init la ++ "→"
      name2 = "→" ++ init la
      namep = init la ++ "'"
      nameq = init la ++ "''"
      name = init la
      lc = last la

bundleSize :: Int
bundleSize = 1 + length (allItems :: [Slot]) -- 1 bit for quarter

varsForDoubleQuarter :: Subject -> (Int, Int)
varsForDoubleQuarter s@(subjectNumber -> Right _) = error "varsForDoubleQuarter"
varsForDoubleQuarter s@(subjectNumber -> Left n) = (base + 1, base + 1)
  where
    base = (n - 1) * bundleSize

varsForSlot :: Subject -> (Int, Int)
varsForSlot s@(subjectNumber -> Right _) = error "varsForSlot"
varsForSlot s@(subjectNumber -> Left n) = (base + 1, base + length (allItems :: [Slot]))
  where
    base = (n -1) * bundleSize + 1

rangeOver :: (Int, Int) -> [Int]
rangeOver (a, b) = [a .. b]

over :: (Subject -> (Int, Int)) -> Subject -> [Int]
over f = rangeOver . f

fromName :: [Subject] -> String -> Subject
fromName subjects l
  | Just x <- find ((l ==) . labelOf) subjects = x
  | otherwise = error ""

on :: Int -> Subject -> Int
on n s@(subjectNumber -> Right _) = error "on"
on n s@(subjectNumber -> Left n') = 1 + (n' - 1) * bundleSize + mod (n - 1) bundleSize

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
            then show ((toEnum pos) :: DoubleQuarter)
            else show (toEnum (pos - numQ) :: Slot)

interprete :: [Int] -> Subject -> (Quarter, Slot)
interprete l s@(subjectNumber -> Right e@(_, q, _, _)) = (q, slotOfEntry e)
interprete l s
  | s' == [] = error $ "no assignment to " ++ labelOf s
  | length s' == 1 = case q' of
    [] | elem (target s) springSems    -> (Q1, head s')
    [] | elem (target s) autumnSems    -> (Q3, head s')
    (x:_) | elem (target s) springSems -> (Q2, head s')
    (x:_) | elem (target s) autumnSems -> (Q4, head s')
  | otherwise = error $ "strange assignment: " ++ show (labelOf s , (q', s'))
  where
    q' = filter (flip elem qs) l
    s' = map toS $ filter (flip elem ss) l
    qs = varsForDoubleQuarter `over` s
    ss = varsForSlot `over` s
    toS x = toEnum . subtract numQ $ mod (abs x - 1) bundleSize
    numQ = 1

as_DoubleQuarter :: Int -> Maybe DoubleQuarter
as_DoubleQuarter (abs -> n)
  | mod (n - 1) bundleSize < 1 = Just (toQ n)
  | otherwise = Nothing
  where
    toQ x = toEnum $ mod (abs x - 1) bundleSize

as_Slot :: Int -> Maybe Slot
as_Slot (abs -> n)
  | 1 < 1 + mod (n - 1) bundleSize = Just (toS n)
  | otherwise = Nothing
  where
    toS x = toEnum . subtract numQ $ mod (abs x - 1) bundleSize
    numQ = 1

as_DoW :: Int -> Maybe Int
as_DoW (abs -> n)
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
                    | q <- varsForDoubleQuarter `over` s1
                    , s <- varsForSlot `over` s1
                    , s1 /= s2  -- for fail-safe
                    ]

--------------------------------------------------------------------------------
-- RULES
--------------------------------------------------------------------------------

-- | 講師は同一時間帯は持てない
rest1 :: [Subject] -> BoolForm
rest1 ss = (-&&&-) [ sub' <!> sub
                   | sub <- subs
                   , lecturer <- lecturersOf sub
                   , sub' <- filter (elem lecturer . lecturersOf) subs
                   , sub < sub'
                   ]
           -&-                  -- 固定科目との整合性
           (-&&&-) [ neg q -|- neg s
                   | sub <- subs
                   , lect <- lecturersOf sub
                   , sub'@(subjectNumber -> Right (_, qu, dow, num)) <- filter (elem lect . lecturersOf) fixed
                   , q <- varsForDoubleQuarter `over` sub
                   , as_DoubleQuarter q == Just (if elem qu [Q1, Q3] then DQ1 else DQ2)
                   , s <- varsForSlot `over` sub
                   , as_Slot s == Just (toSlot dow num)
                   ]
  where
    fixed = filter isFixed ss
    subs  = filter (not . isFixed) ss

-- | 固定科目は同一学年の全科目割当て不可
rest2 :: [Subject] -> BoolForm
rest2 ss = (-&&&-) [ (if elem q' [Q1, Q3] then toBF q else neg q) -|- neg s
                   | sub <- subs
                   , (y', q', d', h') <- map (\(subjectNumber -> Right e) -> e) fixed
                   , seasonOfSubject sub == seasonOf q'
                   , yearOfSubject sub == y'
                   , q <- varsForDoubleQuarter `over` sub
                   , s <- varsForSlot `over` sub
                   , (dowOf <$> as_Slot s) == Just d'
                   , (hourOf <$> as_Slot s) == Just h'
                   ]
  where
    fixed = filter isFixed ss
    subs  = filter (not . isFixed) ss

-- | 第2学年は月火がだめ、第4学年は月がだめ
cond1 ss = (-&&&-) [ neg s
                   | sub <- subs
                   , elem (target sub) [B2A, B2B]
                   , s <- varsForSlot `over` sub
                   , elem (as_Slot s) [Just s | s <- [Mo1 .. Tu5]]
                   ]
           -&-
           (-&&&-) [ neg s -&- neg q
                   | sub <- subs
                   , elem (target sub) [B4A]
                   , q <- varsForDoubleQuarter `over` sub
                   , s <- varsForSlot `over` sub
                   , elem (as_Slot s) [Just s | s <- [Mo1 .. Mo5]]
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | 全てのSubjectの割当ては単一であること
cond2 ss = (-&&&-) [ neg s1 -|- neg s2
                   | sub <- subs
                   , s1 <- varsForSlot `over` sub
                   , s2 <- varsForSlot `over` sub
                   , s1 < s2
                   ]
           -&-
           (-&&&-)[ (-|||-) [ toBF s | s <- varsForSlot `over` sub] | sub <- subs ]
  where
    subs  = filter (not . isFixed) ss

-- | 同学年内では同じ割当てが2回出現することはない
cond3 ss = (-&&&-) [ sub <!> sub'
                   | sub  <- subs
                   , sub' <- subs
                   , target sub == target sub'
                   , sub < sub'
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | nコマの科目は次の連続する(n-1)コマが存在するコマでなければならない
cond4 ss = (-&&&-) [ neg s
                   | sub <- filter ((Nothing /=) . isLong) subs
                   , s <- varsForSlot `over` sub
                   , case isLong sub of
                     Just 2 -> (succSlot =<< as_Slot s) == Nothing
                     Just 3 -> (succSlot =<< succSlot =<< as_Slot s) == Nothing
                     _ -> False
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | nコマの科目はそれらのコマにも同学年の他の科目が入ってはいけない
cond5 ss = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg (s' `on` sub')
                   | sub <- filter ((Nothing /=) . isLong) subs
                   , q <- varsForDoubleQuarter `over` sub
                   , s <- varsForSlot `over` sub
                   , sub' <- subs
                   , target sub == target sub'
                   , sub /= sub'
                   , s' <- varsForSlot `over` sub'
                   , (succSlot =<< as_Slot s) /= Nothing
                   , case isLong sub of
                     Just 2 -> as_Slot s' == (succSlot =<< as_Slot s)
                     Just 3 -> as_Slot s' == (succSlot =<< as_Slot s) || as_Slot s' == (succSlot =<< succSlot =<< as_Slot s)
                     _ -> False
                     ]
  where
    subs  = filter (not . isFixed) ss

-- | 前件科目のチェック
cond6 ss = (-&&&-) [ neg q' -&- q
                   | sub <- filter (([] /=) . preqsOf) subs
                   , sub' <- map (fromName subs) (preqsOf sub)
                   , q <- varsForDoubleQuarter `over` sub
                   , q' <- varsForDoubleQuarter `over` sub'
                   -- , Just True == ((<=) <$> as_DoubleQuarter q <*> as_DoubleQuarter q')
                   ]
           -&-                  -- →を除いた名前が同一の科目対は同校時開講であること
           (-&&&-) [ s -=- (s `on` sub')
                   | sub <- filter (([] /=) . preqsOf) subs
                   , sub' <- map (fromName subs) (preqsOf sub)
                   , delete '→' (labelOf sub) == delete '→' (labelOf sub)
                   , s <- varsForSlot `over` sub
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | 同時開講科目のチェック
cond7 ss = (-&&&-) [ q -=- (q `on` sub')
                   | sub <- filter (([] /=) . sameWith) subs
                   , sub' <- map (fromName subs) (sameWith sub)
                   , sub /= sub'
                   , q <- varsForDoubleQuarter `over` sub
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | 演習室はひとつしかない
cond8 ss = (-&&&-) [ sub' <!> sub
                   | sub <- filter atComputerRoom subs
                   , sub' <- filter atComputerRoom subs
                   , sub' < sub
                   ]
           -&-                -- nコマ連続科目の処理
           (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg s'
                   | sub <- filter atComputerRoom subs
                   , Nothing /= isLong sub
                   , q <- varsForDoubleQuarter `over` sub
                   , s <- varsForSlot `over` sub
                   , sub' <- filter atComputerRoom subs
                   , sub' /= sub
                   , s' <- varsForSlot `over` sub'
                   , (succSlot =<< as_Slot s) /= Nothing
                   , case isLong sub of
                     Just 2 -> as_Slot s' == (succSlot =<< as_Slot s)
                     Just 3 -> as_Slot s' == (succSlot =<< as_Slot s) || as_Slot s' == (succSlot =<< succSlot =<< as_Slot s)
                     _ -> False
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | 3,4年の講義に関しては講師は1日に2つ講義を持たない
cond9 ss = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg s'
                   | sub <- subs
                   , elem (target sub) [B2A ..]
                   , lecturer <- lecturersOf sub
                   , sub' <- subs
                   , elem (target sub') [B2A ..]
                   , sub < sub'
                   , elem lecturer (lecturersOf sub')
                   , q <- varsForDoubleQuarter `over` sub
                   , s <- varsForSlot `over` sub
                   , s' <- varsForSlot `over` sub'
                   , as_DoW s == as_DoW s'
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | 第3学年DQ2に必修はいれない
cond10 ss = (-&&&-) [ neg q
                    | sub <- filter required subs
                    , target sub == B3A
                    , q <- varsForDoubleQuarter `over` sub
                    -- , s <- varsForSlot `over` sub
                    -- , elem (as_DoubleQuarter q, as_Slot s) [(Just DQ2, Just s) | s <- allItems]
                    ]
  where
    subs  = filter (not . isFixed) ss

defaultRules :: [[Subject] -> BoolForm]
defaultRules = [rest1, rest2, cond1, cond2, cond3, cond4, cond5, cond6, cond7, cond8, cond9]

checkConsistenry subjects
  | [] /= invalidPreqs = error $ "`preqs` contains non-existing subject: " ++ head invalidPreqs
  | [] /= invalidSames = error $ "`same` contains non-existing subject: " ++ head invalidSames
  | any ([] ==) (map lecturersOf subjects) = error $ "subject without lecturer: " ++ show (filter (([] ==) . lecturersOf) subjects)
  | [] /= out1 = error $ "春学期内で順序が閉じてない: " ++ head out1
  | [] /= out2 = error $ "秋学期内で順序が閉じてない: " ++ head out2
  | 23 < length lects = error $ "too many lecturers:" ++ intercalate "," lects
  | otherwise = True
  where
    labels = sort $ map labelOf subjects
    preqs = sort $ nub $ concatMap preqsOf subjects
    invalidPreqs = preqs \\ labels
    sames = sort $ nub $ concatMap sameWith subjects
    invalidSames = sames \\ labels
    subAs = filter (flip elem springSems . target) subjects
    subBs = filter (flip elem autumnSems . target) subjects
    out1 = (nub $ concatMap preqsOf subAs) \\ map labelOf subAs
    out2 = (nub $ concatMap preqsOf subBs) \\ map labelOf subBs
    n = length subjects
    lects = nub $ concatMap lecturersOf subjects

splitBySeason subs = (
    renumber $ filter ((flip elem springSems) . target) subs
  , renumber $ filter ((flip elem autumnSems) . target) subs
  )

runSolver :: String -> ([Subject] -> BoolForm) -> [Subject] -> IO ()
runSolver dataName mkrule subjects = do
  os <- getArgs
  let (subjectsInSpring, subjectsInAutomn) = splitBySeason subjects
  unless (checkConsistenry subjectsInSpring) $ error "exit"
  unless (checkConsistenry subjectsInAutomn) $ error "exit"
  let (r1, r2) = (mkrule subjectsInSpring, mkrule subjectsInAutomn)
  let
    seasonIs s (subjectNumber -> Right e) = seasonOfEntry e == s
    seasonIs _ _ = error "seasonIs"
  let
    printer :: [Subject] -> [Int] -> IO ()
    printer subs ans = do
        let x = filter (0 <) . (take (length subs * bundleSize)) $ ans
        let comp (p1, s1) (p2, s2) = case compare (target s1) (target s2) of { EQ -> compare p1 p2; x -> x }
        let l = sortBy comp $ map (\s -> (interprete x s, s)) subs
        let b1l = filter (flip elem [B1A, B1B] . target . snd) l
        let b2l = filter (flip elem [B2A, B2B] . target . snd) l
        let b3l = filter (flip elem [B3A, B3B] . target . snd) l
        let b4l = filter (flip elem [B4A] . target . snd) l
        forM_ [(Y1, b1l), (Y2, b2l), (Y3, b3l), (Y4, b4l)] $ \(y, yl) -> do
          putStrLn $ "### " ++ show y
          forM_ yl $ \((q, r), s) -> do
            putStr $ printf "%s %s: %-24s" (show q) (show r) (labelOf s)
            putStrLn . ("\t" ++) . intercalate ", " $ lecturersOf s
  let
    makeTable :: Season -> [Subject] -> [Int] -> IO ()
    makeTable season subs ans = do
        let x = filter (0 <) . (take (length subs * bundleSize)) $ ans
        let comp (p1, s1) (p2, s2) = case compare (target s1) (target s2) of { EQ -> compare p1 p2; x -> x }
        let l = sortBy comp $ map (\s -> (interprete x s, s)) subs
        let fixed = tableOfFixed $ filter (seasonIs season) $ filter isFixed subjects
        let table = fixed ++ (flip map l $ \((q, slot), subject) -> ((yearOfSubject subject, q, dowOf slot, hourOf slot), subject))
        let h = if season == Spring then "timetable-spring.tex" else "timetable-automn.tex"
        -- toLatexTable p table
        withFile h WriteMode $ toLatex dataName season table
  case os of
    ("-i":_) | elem "B" os -> do
      printer subjectsInAutomn . read =<< getContents
    ("-i":_) -> do
      printer subjectsInSpring . read =<< getContents
    ("-d":_) -> do
      putStrLn . asCNFString $ if elem "B" os then r2 else r1
    _ -> do
      let anss = map (SAT.satisfiable (:) . asList) [r1, r2]
      forM_ (zip3 [Spring, Autumn] anss [subjectsInSpring, subjectsInAutomn]) $ \(season, res, subs) -> do
        putStr $ "-------- " ++ if season == Spring then "春学期" else "秋学期"
        let bf = if season == Spring then r1 else r2
        putStrLn $ "; " ++ show (numberOfVariables bf, numberOfClauses bf)
        case res of
          [] -> putStrLn "can't solve"
          (r:_) -> printer subs r >> makeTable (season :: Season) subs r

toLatex :: String -> Season -> TimeTable -> Handle -> IO ()
toLatex dataName season table h = do
  when (season == Spring) (hPutStrLn h . printf "\\newcommand{\\versionID}{%s (%s)}" dataName =<< currentTimeString)
  forM_ tags $ \(k@(_, q, _, _), s) -> do
    let dq = if elem q [Q1, Q3] then DQ1 else DQ2
    case find ((k ==) . fst) table of
      Just (_, sub) -> do
        let name = labelOf sub
        let lecs' = intercalate "," $ lecturersOf sub
        let lecs = if 5 < length lecs' then "\\tiny " ++ lecs' else lecs'
        case (required sub, atComputerRoom sub) of
          (True , True ) -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\cellcolor{blue!10}\\textcolor{red}{\\textbf{%s}}}" p s name
          (True , False) | dq == DQ1 -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\textcolor{red}{\\textbf{%s}}}" p s name
          (True , False) | dq == DQ2 -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\cellcolor{black!5}\\textcolor{red}{\\textbf{%s}}}" p s name
          (False, True ) -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\cellcolor{blue!10}%s}" p s name
          (False, False) | dq == DQ1 -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{%s}" p s name
          (False, False) | dq == DQ2 -> hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\cellcolor{black!5}%s}" p s name
          _ -> putStrLn $ "unhandled pattern: " ++ show (labelOf sub) ++ " @ " ++ show q
        if dq == DQ1
          then hPutStrLn h $ printf "\\newcommand{\\%s%sLec}{\\footnotesize %s}" p s lecs
          else hPutStrLn h $ printf "\\newcommand{\\%s%sLec}{\\cellcolor{black!5}\\footnotesize %s}" p s lecs
      _ | follwingCell k -> do
        hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\cellcolor{blue!10}\\hfil↑\\hfil}" p s
        if dq == DQ1
          then hPutStrLn h $ printf "\\newcommand{\\%s%sLec}{}" p s
          else hPutStrLn h $ printf "\\newcommand{\\%s%sLec}{\\cellcolor{black!5}}" p s
      _ | dq == DQ1 -> do
        hPutStr h $ printf "\\newcommand{\\%s%sSub}{}" p s
        hPutStrLn h $ printf "\\newcommand{\\%s%sLec}{}" p s
      _ -> do
        hPutStr h $ printf "\\newcommand{\\%s%sSub}{\\cellcolor{black!5}}" p s
        hPutStrLn h $ printf "\\newcommand{\\%s%sLec}{\\cellcolor{black!5}}" p s
  where
    follwingCell (y, q, d, h)
      | elem h [H1, H3] = False
      | Just (_, sub) <- find ((k' ==) . fst) table = Nothing /= isLong sub && atComputerRoom sub
      | elem h [H2, H4] = False
      | Just (_, sub) <- find ((k'' ==) . fst) table = Just 3 == isLong sub  && atComputerRoom sub
      | otherwise = False
      where
        k' = (y, q, d, pred h)
        k'' = (y, q, d, pred (pred h))
    p :: String
    p = if season == Spring then "Sp" else "Au"
    tags = [ ( (y, q, d, h)
             , (printf "%s%s%s%s" (yp y) (qp q) (show d) (hp h)) :: String)
           | y <- [minBound :: Year .. maxBound]
           , q <- [minBound :: Quarter .. maxBound]
           , d <- [minBound :: DoW .. maxBound]
           , h <- [minBound :: Hour .. maxBound]
           ]
    yp :: Year -> String
    yp Y1 = "One"
    yp Y2 = "Two"
    yp Y3 = "Thr"
    yp Y4 = "Fou"
    qp :: Quarter -> String
    qp Q1 = "Qone"
    qp Q2 = "Qtwo"
    qp Q3 = "Qthr"
    qp Q4 = "Qfou"
    hp :: Hour -> String
    hp H1 = "One"
    hp H2 = "Two"
    hp H3 = "Thr"
    hp H4 = "Fou"
    hp H5 = "Fiv"

toLatexTable :: String -> [(Subject, Entry, (String, [String]))] -> IO ()
toLatexTable p _ = do
  forM_ (allItems :: [DoW]) $ \d -> do
    forM_ (allItems :: [Hour]) $ \s -> do
      putStr $ "&" ++ show (fromEnum s + 1) ++ "&"
      forM_ (allItems :: [Year]) $ \y -> do
        forM_ (allItems :: [Quarter]) $ \q -> do
          putStr ((printf "\\%s%s%s%s%sSub&" p (show y) (show q) (show d) (show s)) :: String)
          putStr ((printf "\\%s%s%s%s%sLec" p (show y) (show q) (show d) (show s)) :: String)
          if q == maxBound && y == Y1 then putStrLn "\\\\\\hline" else putStr "&"

currentTimeString :: IO String
currentTimeString = do
  t <- utcToLocalTime <$> (getTimeZone =<< getCurrentTime) <*> getCurrentTime
  return $ formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" t

tableOfFixed :: [Subject] -> TimeTable
tableOfFixed l = map (\s@(subjectNumber -> Right e) -> (e, s)) $ filter isFixed l
