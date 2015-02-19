{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module Timetable.Types
       (
         module SAT.CNFIO
       , LectureYear (..)
       , LectureDate (..)
       , LectureHour (..)
       , Year (..)
       , Season (..)
       , Quarter (..)
       , DoW (..)
       , Hour (..)
       , Target (..)
       , Slot (..)
       , quarterVars
       , slotVars
       , succSlot
       , Subject (..)
       , Sub (..)
       , TimeTable
       , over
       , on
       , canonize
       , renumber
       , isFixed
       , allItems
       , asEntry
       , bitsForSubject
       , (<!>)
       , anotherQuarterBool
       , shareSlot
       , fromName
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

-- fundamental types

allItems :: (Bounded a, Enum a) => [a]
allItems = [minBound.. maxBound]

data Year = Y1 | Y2 | Y3 | Y4 deriving (Bounded, Enum, Eq, Ord, Show)
data Season = Spring | Autumn deriving (Bounded, Enum, Eq, Ord, Show)
data Quarter = Q1 | Q2 | Q3 | Q4 deriving (Bounded, Enum, Eq, Ord, Show)

dateBits :: Int
dateBits = 1

data DoW = Mon | Tue | Wed | Thu | Fri deriving (Bounded, Enum, Eq, Ord, Show)
data Hour = H1 | H2 | H3 | H4 | H5 deriving (Bounded, Enum, Eq, Ord, Show)
data Slot = Slot DoW Hour deriving (Eq, Ord)

instance Show Slot where
  show (Slot Mon h) = "月" ++ show (fromEnum h + 1)
  show (Slot Tue h) = "火" ++ show (fromEnum h + 1)
  show (Slot Wed h) = "水" ++ show (fromEnum h + 1)
  show (Slot Thu h) = "木" ++ show (fromEnum h + 1)
  show (Slot Fri h) = "金" ++ show (fromEnum h + 1)

validSlot = [ Slot d h
            | d <- [Mon .. Fri]
            , h <- [H1 .. H5]
            , notElem (d, h) [(Wed, H5), (Fri, H5)]
            ]

instance Bounded Slot where
  minBound = head validSlot
  maxBound = last validSlot

instance Enum Slot where
  toEnum n = validSlot !! (n - 1)
  fromEnum k = loop validSlot 1
    where
      loop [] _ = error "out of range for Slot"
      loop (x:l) n = if k == x then n else loop l (n + 1)

succSlot :: Slot -> Maybe Slot
succSlot s@(Slot d h)
  | elem h [H2, H5] = Nothing
  | d == Wed && h == H4 = Nothing
  | d == Fri && h == H4 = Nothing
  | otherwise = Just $ succ s

type Entry = (Year, Quarter, Slot)

data Target
  = TargetSeason Year Season
  | TargetQuarter Year Quarter
  | TargetFixed Entry
  | S Year Season
  | Q Year Quarter
  | F Year Quarter DoW Hour
    deriving (Eq, Ord, Show)

data Subject = Subject
               {
                 labelOf :: String -- ^ 科目名
               , target :: Target  -- ^ 開講時期
               , required :: Bool  -- ^ 必修/選択
               , lecturersOf :: [String] -- ^ 担当教員群
               , isLong :: Int     	-- ^ 連続コマ数
               , preqsOf :: [String]     -- ^ 履修条件
               , sameWith :: [String]    -- ^ 同時開講科目
               , atComputerRoom :: Bool    -- ^ 演習室使用
               , subjectNumber :: Either Int Entry
               }
               deriving (Eq, Ord, Show)

hourBits :: Int
hourBits = 1 + fromEnum (maxBound :: Slot)

bitsForSubject :: Int
bitsForSubject = dateBits + hourBits

-- | zero-based
indexFromVar :: Int -> Int
indexFromVar n = mod (n - 1) bitsForSubject

class LectureYear a where
  asYear :: a -> Year

instance LectureYear Year where
  asYear = id

instance LectureYear Entry where
  asYear (y, _, _) = y

instance LectureYear Target where
  asYear (TargetSeason y _) = y
  asYear (TargetQuarter y _) = y
  asYear (TargetFixed e) = asYear e

instance LectureYear Subject where
  asYear = asYear . target

class LectureDate a where
  asSeason :: a -> Season
  asQuarter :: a -> Quarter

instance LectureDate Season where
  asSeason  = id
  asQuarter = error "can't cast to `Quarter` from `Season`"

instance LectureDate Quarter where
  asSeason Q1	= Spring
  asSeason Q2	= Spring
  asSeason Q3	= Autumn
  asSeason Q4	= Autumn
  asQuarter 	= error "can't cast to `Quarter` from `Season`"

instance LectureDate Entry where
  asSeason (_, q, _) = asSeason q
  asQuarter (_, q, _) = q

instance LectureDate Target where
  asSeason (TargetSeason _ s)	= s
  asSeason (TargetQuarter _ q)	= asSeason q
  asSeason (TargetFixed e)	= asSeason e
  asQuarter (TargetSeason _ s)	= error "can't convert from seanson info."
  asQuarter (TargetQuarter _ q)	= q
  asQuarter (TargetFixed e)	= asQuarter e

instance LectureDate Subject where
  asSeason  = asSeason . target
  asQuarter = asQuarter . target

instance LectureDate (Subject, Int) where
  asSeason = asSeason . fst
  asQuarter (s, i) = error "our coding system can't hold the quater information"
--    | asSeason s == Spring = toEnum $ indexFromVar i
--    | asSeason s == Autumn = toEnum $ 2 + indexFromVar i

class LectureHour a where
  asSlot :: a -> Slot
  asDoW :: a -> DoW
  asHour :: a -> Hour

instance LectureHour Slot where
  asSlot = id
  asDoW (Slot d _) = d
  asHour (Slot _ h) = h

instance LectureHour Entry where
  asSlot (_, _, s) = s
  asDoW (_, _, s) = asDoW s
  asHour (_, _, s) = asHour s

instance LectureHour (Subject, Int) where
  asSlot (s, i)
    | Right e <- subjectNumber s = asSlot e
    | start < i && i <= start + bitsForSubject = toEnum $ indexFromVar i
    where
       (Left nth) = subjectNumber s
       start = bitsForSubject * (nth - 1)
  asDoW = asDoW . asSlot
  asHour = asHour . asSlot

isFixed :: Subject -> Bool
isFixed (subjectNumber -> Left _) = False
isFixed (subjectNumber -> Right _) = True

type TimeTable = [(Entry, Subject)]

data Sub = Sub String Target Bool [String] Int [String] [String] Bool

canonize :: [Sub] -> [Subject]
canonize = renumber . concatMap unfoldSubject

renumber :: [Subject] -> [Subject]
renumber l = loop l 1
  where
    loop [] _                         = []
    loop (sub@(isFixed -> True):l)  n = sub                            : loop l n
    loop (sub@(isFixed -> False):l) n = sub { subjectNumber = Left n } : loop l (n + 1)

unfoldSubject sub@(Sub la (F y q d h) re ls is pr sa at)
  = [Subject la (TargetFixed e) re ls is pr sa at (Right e)]
  where
    e = (y, q, Slot d h)
unfoldSubject sub@(Sub la (Q y q) re ls is pr sa at)
  -- 科目名が'で終わると同時開講
  | lc == '\''  = [Subject namep ta re ls is pr sa at z, Subject nameq ta re ls is pr [namep] at z]
  -- 科目名が*で終わると2クォーター開講
  | lc == '+'   = [Subject name1 ta re ls is pr sa at z, Subject name2 ta re ls is [name1] sa at z]
  -- 科目名が?で終わると2コマ必要
  | lc == '?'   = [Subject name  ta re ls is pr sa at z, Subject (name ++ "?") ta re ls is pr sa at z]
  | otherwise   = [Subject la ta re ls is pr sa at z]
    where
      ta = TargetQuarter y q
      z = Left 0
      name1 = init la ++ "→"
      name2 = "→" ++ init la
      namep = init la ++ "'"
      nameq = init la ++ "''"
      name = init la
      lc = last la
unfoldSubject sub@(Sub la (S y s) re ls is pr sa at)
  -- 科目名が'で終わると同時開講
  | lc == '\''  = [Subject namep ta re ls is pr sa at z, Subject nameq ta re ls is pr [namep] at z]
  -- 科目名が*で終わると2クォーター開講
  | lc == '+'   = [Subject name1 ta re ls is pr sa at z, Subject name2 ta re ls is [name1] sa at z]
  -- 科目名が?で終わると2コマ必要
  | lc == '?'   = [Subject name  ta re ls is pr sa at z, Subject (name ++ "?") ta re ls is pr sa at z]
  | otherwise   = [Subject la ta re ls is pr sa at z]
    where
      ta = TargetSeason y s
      z = Left 0
      name1 = init la ++ "→"
      name2 = "→" ++ init la
      namep = init la ++ "'"
      nameq = init la ++ "''"
      name = init la
      lc = last la
unfoldSubject _ = error "please use one of F, S or Q"

quarterVars :: Subject -> (Int, Int)
quarterVars s@(subjectNumber -> Right _) = error $ "quarterVars on fixed lecture:"  ++ labelOf s
quarterVars s@(subjectNumber -> Left n) = (base + 1, base + 1)
  where
    base = (n - 1) * bitsForSubject

slotVars :: Subject -> (Int, Int)
slotVars s@(subjectNumber -> Right _) = error "varsForSlot"
slotVars s@(subjectNumber -> Left n) = (base + 1, base + length (allItems :: [Slot]))
  where
    base = (n -1) * bitsForSubject + 1

rangeOver :: (Int, Int) -> [Int]
rangeOver (a, b) = [a .. b]

over :: (Subject -> (Int, Int)) -> Subject -> [Int]
over f = rangeOver . f

on :: Int -> Subject -> Int
on n s@(subjectNumber -> Right _) = error "on"
on n s@(subjectNumber -> Left n') = 1 + (n' - 1) * bitsForSubject + mod (n - 1) bitsForSubject

fromName :: [Subject] -> String -> Subject
fromName subjects l
  | Just x <- find ((l ==) . labelOf) subjects = x
  | otherwise = error ""

asEntry :: (Subject, [Int]) -> Entry
asEntry (fst -> subjectNumber -> Right e) = e
asEntry (s, l)
  | s' == [] = error $ "no assignment to " ++ labelOf s
  | length s' == 1 = case q' of
    [] | asSeason s == Spring    -> (asYear s, Q1, asSlot (s, (head s')))
    [] | asSeason s == Autumn    -> (asYear s, Q3, asSlot (s, (head s')))
    (x:_) | asSeason s == Spring -> (asYear s, Q2, asSlot (s, (head s')))
    (x:_) | asSeason s == Autumn -> (asYear s, Q4, asSlot (s, (head s')))
  | otherwise = error $ "strange assignment: " ++ labelOf s ++ show (q', map (\i -> asSlot (s, i)) s')
  where
    q' = filter (flip elem qs) l
    s' = filter (flip elem ss) l
    qs = quarterVars `over` s
    ss = slotVars `over` s
    numQ = 1

-- | imcompatible relation
(<!>) :: Subject -> Subject -> BoolForm
s1 <!> s2
  | isFixed s1 = error "the first arg of (<!>) is fixed"
  | otherwise = (-&&&-) [ (q -!- (q `on` s2)) -|- neg s -|- neg (s `on` s2)
                        | q <- quarterVars `over` s1
                        , s <- slotVars `over` s1
                        , asSeason s1 == asSeason s2
                        , s1 /= s2  -- for fail-safe
                        ]

anotherQuarterBool :: Subject -> Subject -> BoolForm
anotherQuarterBool s s'
  | isFixed s && isFixed s' = error $ "anotherQuarterBool accepts fixed lectures: " ++ labelOf s ++ " and " ++ labelOf s'
  | Right _ <- subjectNumber s = case asQuarter s of -- もし固定科目ならその反対
    Q1 -> toBF j
    Q2 -> neg j
    Q3 -> toBF j
    Q4 -> neg j
  | Right _ <- subjectNumber s' = case asQuarter s' of -- もし固定科目ならその反対
    Q1 -> toBF i
    Q2 -> neg i
    Q3 -> toBF i
    Q4 -> neg i
  | asSeason s == asSeason s' = i -!- j         -- そうでなく季節が同じなら変数間制約
  | otherwise = toBF True                       -- 季節が違う場合は無視
  where
    i = head $ quarterVars `over` s
    j = head $ quarterVars `over` s'

shareSlot :: (LectureHour d1, LectureHour d2) => (Subject, d1) -> (Subject, d2) -> Bool
shareSlot (sub1, (asSlot -> s1)) (sub2, (asSlot -> s2)) =
  case isLong sub1 of
    1 ->
      case isLong sub2 of
        1 -> s1 == s2
        2  -> s1 == s2 || Just s1 == succSlot s2
        3  -> s1 == s2 || Just s1 == (succSlot s2) || Just s1 == (succSlot =<< succSlot s2)
    2  -> s1 == s2 || Just s2 == succSlot s1
    3  -> s1 == s2 || Just s2 == (succSlot s1) || Just s2 == (succSlot =<< succSlot s1)
