{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Timetable
       (
         module SAT.CNFIO
       , module Timetable.Types
       , defaultRules
       , runSolver
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
                   , asSlot (sub, s) == slot'
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

-- | 同学年内では同じ割当てが2回出現することはない
cond4 ss = (-&&&-) [ sub <!> sub'
                   | sub  <- subs
                   , sub' <- subs
                   , asYear sub == asYear sub'
                   , sub < sub'
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | nコマの科目は次の連続する(n-1)コマが存在するコマでなければならない
cond5 ss = (-&&&-) [ neg s
                   | sub <- filter ((Nothing /=) . isLong) subs
                   , s <- slotVars `over` sub
                   , case isLong sub of
                     Just 2 -> succSlot (asSlot (sub, s)) == Nothing
                     Just 3 -> (succSlot =<< succSlot (asSlot (sub, s))) == Nothing
                     _ -> False
                   ]
  where
    subs  = filter (not . isFixed) ss

{-
-- | nコマの科目はそれらのコマにも同学年の他の科目が入ってはいけない
cond6 ss = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg (s' `on` sub')
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
cond7 ss = (-&&&-) [ neg q' -&- q
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
cond8 ss = (-&&&-) [ q -=- (q `on` sub')
                   | sub <- filter (([] /=) . sameWith) subs
                   , sub' <- map (fromName subs) (sameWith sub)
                   , sub /= sub'
                   , q <- varsForDoubleQuarter `over` sub
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | 演習室はひとつしかない
cond9 ss = (-&&&-) [ sub' <!> sub
                   | sub <- filter atComputerRoom subs
                   , sub' <- filter atComputerRoom subs
                   , sub' < sub
                   ]
           -&-                  --
           (-&&&-) [ (if elem q' [Q1, Q3] then toBF q else neg q) -|- neg s
                   | sub <- filter atComputerRoom subs
                   , (y', q', d', h') <- map (\(subjectNumber -> Right e) -> e) (filter atComputerRoom fixed)
                   , q <- varsForDoubleQuarter `over` sub
                   , s <- varsForSlot `over` sub
                   , (dowOf <$> as_Slot s) == Just d'
                   , (hourOf <$> as_Slot s) == Just h'
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
           -&-                  --
           (-&&&-) [ (if elem q' [Q1, Q3] then toBF q else neg q) -|- neg s
                   | sub <- filter atComputerRoom subs
                   , (sub', (_, q', d', h')) <- map (\s@(subjectNumber -> Right e) -> (s, e)) (filter atComputerRoom fixed)
                   , q <- varsForDoubleQuarter `over` sub
                   , s <- varsForSlot `over` sub
                   , (dowOf <$> as_Slot s) == Just d'
                   , case isLong sub' of
                     Just 2 -> (hourOf <$> as_Slot s) == Just (succ h')
                     Just 3 -> (hourOf <$> as_Slot s) == Just (succ h') || (hourOf <$> as_Slot s) == Just (succ $ succ h')
                     _ -> False
                   ]
  where
    subs  = filter (not . isFixed) ss
    fixed = filter isFixed ss

{-
-- | 第2学年は月火がだめ、第4学年は月がだめ
cond10 ss = (-&&&-) [ neg s
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
-}

-- | 3,4年の講義に関しては講師は1日に2つ講義を持たない
cond11 ss = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg s'
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
cond12 ss = (-&&&-) [ neg q
                    | sub <- filter required subs
                    , target sub == B3A
                    , q <- varsForDoubleQuarter `over` sub
                    -- , s <- varsForSlot `over` sub
                    -- , elem (as_DoubleQuarter q, as_Slot s) [(Just DQ2, Just s) | s <- allItems]
                    ]
  where
    subs  = filter (not . isFixed) ss
-}

defaultRules :: [[Subject] -> BoolForm]
defaultRules = [cond1, cond2, cond3, cond4, cond5]
-- defaultRules = [rest1, rest2, cond1, cond2, cond3, cond4, cond5, cond6, cond7, cond8, cond9, cond10]

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
    subAs = filter ((Spring ==) . asSeason) subjects
    subBs = filter ((Autumn ==) . asSeason) subjects
    out1 = (nub $ concatMap preqsOf subAs) \\ map labelOf subAs
    out2 = (nub $ concatMap preqsOf subBs) \\ map labelOf subBs
    n = length subjects
    lects = nub $ concatMap lecturersOf subjects

splitBySeason subs = (
    renumber $ filter ((Spring ==) . asSeason) subs
  , renumber $ filter ((Autumn ==) . asSeason) subs
  )

runSolver :: String -> ([Subject] -> BoolForm) -> [Subject] -> IO ()
runSolver dataName mkrule subjects = do
  os <- getArgs
  let (subjectsInSpring, subjectsInAutomn) = splitBySeason subjects
  unless (checkConsistenry subjectsInSpring) $ error "exit"
  unless (checkConsistenry subjectsInAutomn) $ error "exit"
  let (r1, r2) = (mkrule subjectsInSpring, mkrule subjectsInAutomn)
  let
    seasonIs season sub = season == asSeason sub
  let
    assignTable :: Season -> [Subject] -> [Int] -> TimeTable
    assignTable season subs ans = table
      where
        x = filter (0 <) . (take (length subs * bitsForSubject)) $ ans
        comp (p1, s1) (p2, s2) = case compare (target s1) (target s2) of { EQ -> compare p1 p2; x -> x }
        table = sortBy comp $ map (\s -> (asEntry (s, x), s)) subs
  let
    printer :: Season -> [Subject] -> [Int] -> IO ()
    printer season subs ans = do
        forM_ [Y1 .. Y4] $ \y -> do
          putStrLn $ "### " ++ show y
          forM_ (assignTable season subs ans) $ \(e, s) -> do
            when (asYear e == y) $ do
              putStr $ printf "%s: %-24s" (show (asSlot e)) (labelOf s)
              putStrLn . ("\t" ++) . intercalate ", " $ lecturersOf s
  let
    makeTable :: Season -> [Subject] -> [Int] -> IO ()
    makeTable season subs ans = do
        let h = if season == Spring then "timetable-spring.tex" else "timetable-automn.tex"
        -- toLatexTable p table
        putStrLn "" -- withFile h WriteMode $ toLatex dataName season (assignTable season subs ans)
  case os of
    ("-i":_) | elem "B" os -> do
      printer Autumn subjectsInAutomn . read =<< getContents
    ("-i":_) -> do
      printer Spring subjectsInSpring . read =<< getContents
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
          (r:_) -> printer season subs r -- >> makeTable (season :: Season) subs r
      when (not (null (anss !! 0)) && not (null (anss !! 0))) $ do
        let fulltable = concat [ assignTable s sub (head ans)
                               | s <- [Spring, Autumn]
                               | sub <- [subjectsInSpring, subjectsInAutomn]
                               | ans <- anss
                               ]
        dumpReport fulltable      -- summary report

{-
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
-}
dumpReport :: TimeTable -> IO ()
dumpReport table = do
  putStrLn "### load summary"
  forM_ lects $ \lect -> do
    putStr lect
    let subs = gather lect
    putStr . ("\t: " ++) . show . map (\q -> length . filter (\(q', _) -> asQuarter q' == q) $ subs) $ [Q1 .. Q4]
    putStrLn . (" " ++) . intercalate ", " . map (labelOf . snd) $ subs
  where
    lects = sort . nub . concatMap (lecturersOf . snd) $ table
    gather key = filter (elem key . lecturersOf . snd) $ table

