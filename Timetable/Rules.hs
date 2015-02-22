{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Timetable.Rules
       (
         defaultRules
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
import Timetable.Types

--------------------------------------------------------------------------------
-- RULES
--------------------------------------------------------------------------------

-- | 全てのSubjectの割当ては単一であること
cond1 ss = (-&&&-) [ neg s1 -|- neg s2
                   | sub <- subs
                   , s1 <- slotVars `over` sub
                   , s2 <- slotVars `over` sub
                   , s1 < s2
                   ]
           -&-
           (-&&&-)[ (-|||-) [ toBF s | s <- slotVars `over` sub] | sub <- subs ]
  where
    subs  = filter (not . isFixed) ss

-- | 講師は同一時間帯は持てない
cond2 :: [Subject] -> BoolForm
cond2 ss = (-&&&-) [ sub' <!> sub
                   | sub <- subs
                   , lecturer <- lecturersOf sub
                   , sub' <- filter (elem lecturer . lecturersOf) subs
                   , sub < sub'
                   ]
           -&-                  -- 固定科目との整合性
           (-&&&-) [ anotherQuarterBool sub sub' -|- neg s
                   | sub <- subs
                   , lect <- lecturersOf sub
                   , sub'@(subjectNumber -> Right (_, _, slot')) <- filter (elem lect . lecturersOf) fixed
                   , s <- slotVars `over` sub
                   , shareSlot (sub, (sub, s)) (sub', slot')
                   ]
  where
    fixed = filter isFixed ss
    subs  = filter (not . isFixed) ss

-- | 固定科目は同一学年の全科目割当て不可
cond3 :: [Subject] -> BoolForm
cond3 ss = (-&&&-) [ anotherQuarterBool sub sub' -|- neg s
                   | sub <- subs
                   , sub' <- fixed
                   , let Right (y', _, s') = subjectNumber sub'
                   , s <- slotVars `over` sub
                   , (asYear sub, asSlot (sub, s)) == (y', s') -- 学年とスロットが同じならあとはクォーターの検査
                   ]
  where
    fixed = filter isFixed ss
    subs  = filter (not . isFixed) ss

-- | クォーター固定科目の処理
cond4 ss = (-&&&-) [ if elem (asQuarter sub) [Q1, Q3] then neg q else toBF q
                   | sub <- filter isSubQ ss
                   , q <- quarterVars `over` sub
                   ]
  where
    isSubQ sub
      | TargetQuarter _ _ <- target sub = True
      | otherwise = False

-- | 同学年内では同じ割当てが2回出現することはない
cond5 ss = (-&&&-) [ sub <!> sub'
                   | sub  <- subs
                   , sub' <- subs
                   , asYear sub == asYear sub'
                   , sub < sub'
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | nコマの科目は次の連続する(n-1)コマが存在するコマでなければならない
cond6 ss = (-&&&-) [ neg s
                   | sub <- filter ((1 <) . isLong) subs
                   , s <- slotVars `over` sub
                   , case isLong sub of
                     2 -> succSlot (asSlot (sub, s)) == Nothing
                     3 -> (succSlot =<< succSlot (asSlot (sub, s))) == Nothing
                     _ -> False
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | nコマの科目はそれらのコマにも同学年の他の科目が入ってはいけない
cond7 ss = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg (s' `on` sub')
                   | sub <- filter ((1 <) . isLong) subs
                   , q <- quarterVars `over` sub
                   , s <- slotVars `over` sub
                   , sub' <- subs
                   , sub /= sub'
                   , asYear sub == asYear sub'
                   , asSeason sub == asSeason sub'
                   , s' <- slotVars `over` sub'
                   , shareSlot (sub, (sub, s)) (sub', (sub', s'))
                   ]
           -&-
           (-&&&-) [ anotherQuarterBool sub sub' -|- neg s'
                   | sub <- filter ((1 <) . isLong) fixed
                   , let (Right e) = subjectNumber sub
                   , sub' <- subs
                   , asYear e == asYear sub'
                   , asSeason e == asSeason sub'
                   , s' <- slotVars `over` sub'
                   , shareSlot (sub, asSlot e) (sub', (sub', s'))
                   ]
  where
    fixed  = filter isFixed ss
    subs  = filter (not . isFixed) ss


-- | 前件科目のチェック
cond8 ss = (-&&&-) [ neg q' -&- q
                   | sub <- filter (([] /=) . preqsOf) subs
                   , sub' <-filter (not . isFixed) $  map (fromName subs) (preqsOf sub)
                   , q <- quarterVars `over` sub
                   , q' <- quarterVars `over` sub'
                   -- , Just True == ((<=) <$> as_DoubleQuarter q <*> as_DoubleQuarter q')
                   ]
           -&-                  -- →を除いた名前が同一の科目対は同校時開講であること
           (-&&&-) [ s -=- (s `on` sub')
                   | sub <- filter (([] /=) . preqsOf) subs
                   , sub' <- map (fromName subs) (preqsOf sub)
                   , delete '→' (labelOf sub) == delete '→' (labelOf sub)
                   , s <- slotVars `over` sub
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | 同時開講科目のチェック
cond9 ss = (-&&&-) [ q -=- (q `on` sub')
                   | sub <- filter (([] /=) . sameWith) subs
                   , sub' <- map (fromName subs) (sameWith sub)
                   , sub /= sub'
                   , q <- quarterVars `over` sub
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | 演習室はひとつしかない
cond10 ss = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg s'
                    | sub <- filter atComputerRoom subs
                    , sub' <- filter atComputerRoom subs
                    , sub' /= sub
                    , q <- quarterVars `over` sub
                    , s <- slotVars `over` sub
                    , s' <- slotVars `over` sub'
                    , shareSlot (sub, (sub, s)) (sub', (sub', s'))
                    ]
            -&-                  -- 固定科目で演習室を使う科目との整合性検査
            (-&&&-) [ anotherQuarterBool sub sub' -|- neg s
                    | sub <- filter atComputerRoom subs
                    , sub' <- filter atComputerRoom fixed
                    , let (Right (_, _', s')) = subjectNumber sub'
                    , s <- slotVars `over` sub
                    , shareSlot (sub, (sub, s)) (sub', s')
                    ]
  where
    subs  = filter (not . isFixed) ss
    fixed = filter isFixed ss

-- | 第2学年は月火がだめ、第2Qがだめ
cond11 ss = (-&&&-) [ neg s
                    | sub <- filter ((Y2 ==) . asYear) subs
                    , s <- slotVars `over` sub
                    , elem (asDoW (sub, s)) [Mon, Tue]
                    ]
            -&-
            (-&&&-) [ neg q
                    | sub <- filter ((Y4 ==) . asYear) subs
                    , q <- quarterVars `over` sub
                    ]
  where
    subs  = filter (not . isFixed) ss

-- | 3,4年の講義に関しては講師は1日に2つ講義を持たない
cond12 ss = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg s'
                   | sub <- filter ((Y1 <=) . asYear) subs
                   , lecturer <- lecturersOf sub
                   , sub' <- filter ((Y1 <=) . asYear) subs
                   , sub < sub'
                   , elem lecturer (lecturersOf sub')
                   , q <- quarterVars `over` sub
                   , s <- slotVars `over` sub
                   , s' <- slotVars `over` sub'
                   , asDoW (sub, s) == asDoW (sub', s')
                   ]
            -&-
            (-&&&-) [ anotherQuarterBool sub sub' -|- neg s
                   | sub <- filter ((Y1 <=) . asYear) subs
                   , lecturer <- lecturersOf sub
                   , sub' <- filter ((Y1 <=) . asYear) fixed
                   , sub < sub'
                   , elem lecturer (lecturersOf sub')
                   , s <- slotVars `over` sub
                   , let (Right (_, _, s')) = subjectNumber sub'
                   , asDoW (sub, s) == asDoW s'
                   ]
  where
    fixed  = filter isFixed ss
    subs  = filter (not . isFixed) ss

-- | 第3学年DQ2に必修はいれない
cond13 ss = (-&&&-) [ neg q
                    | sub <- subs
                    , asYear sub == Y3 && asSeason sub == Spring && required sub
                    , q <- quarterVars `over` sub
                    ]
  where
    subs  = filter (not . isFixed) ss

defaultRules :: [[Subject] -> BoolForm]
defaultRules = [cond1, cond2, cond3, cond4, cond5, cond6, cond7, cond8, cond9, cond10, cond11, cond12, cond13]
