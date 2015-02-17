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

-- | nコマの科目はそれらのコマにも同学年の他の科目が入ってはいけない
cond6 ss = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg (s' `on` sub')
                   | sub <- filter ((Nothing /=) . isLong) subs
                   , q <- quarterVars `over` sub
                   , s <- slotVars `over` sub
                   , sub' <- subs
                   , sub /= sub'
                   , asYear sub == asYear sub'
                   , asSeason sub == asSeason sub'
                   , s' <- slotVars `over` sub'
                   , shareSlot sub (sub, s) (sub', s')
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | 前件科目のチェック
cond7 ss = (-&&&-) [ neg q' -&- q
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
cond8 ss = (-&&&-) [ q -=- (q `on` sub')
                   | sub <- filter (([] /=) . sameWith) subs
                   , sub' <- map (fromName subs) (sameWith sub)
                   , sub /= sub'
                   , q <- quarterVars `over` sub
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | 演習室はひとつしかない
cond9 ss = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg s'
                   | sub <- filter atComputerRoom subs
                   , sub' <- filter atComputerRoom subs
                   , sub' /= sub
                   , q <- quarterVars `over` sub
                   , s <- slotVars `over` sub
                   , s' <- slotVars `over` sub'
                   , shareSlot sub (sub, s) (sub', s')
                   ]
           -&-                  -- 固定科目で演習室を使う科目との整合性検査
           (-&&&-) [ anotherQuarterBool sub sub' -|- neg s
                   | sub <- filter atComputerRoom subs
                   , sub' <- filter atComputerRoom fixed
                   , let (Right (_, _', s')) = subjectNumber sub'
                   , s <- slotVars `over` sub
                   , shareSlot sub (sub, s) s'
                   ]
  where
    subs  = filter (not . isFixed) ss
    fixed = filter isFixed ss

-- | 第2学年は月火がだめ、第4学年は月、第2Qがだめ
cond10 ss = (-&&&-) [ neg s
                    | sub <- filter ((Y1 ==) . asYear) subs
                    , s <- slotVars `over` sub
                    , elem (asDoW (sub, s)) [Mon, Tue]
                    ]
            -&-
            (-&&&-) [ neg s -&- neg q
                    | sub <- filter ((Y4 ==) . asYear) subs
                    , q <- quarterVars `over` sub
                    , s <- slotVars `over` sub
                    , elem (asDoW (sub, s)) [Mon]
                    ]
            -&-
            (-&&&-) [ neg q
                    | sub <- filter ((Y4 ==) . asYear) subs
                    , q <- quarterVars `over` sub
                    ]
  where
    subs  = filter (not . isFixed) ss

-- | 3,4年の講義に関しては講師は1日に2つ講義を持たない
cond11 ss = (-&&&-) [ (q -!- (q `on` sub')) -|- neg s -|- neg s'
                   | sub <- filter ((Y2 <=) . asYear) subs
                   , lecturer <- lecturersOf sub
                   , sub' <- filter ((Y2 <=) . asYear) subs
                   , sub < sub'
                   , elem lecturer (lecturersOf sub')
                   , q <- quarterVars `over` sub
                   , s <- slotVars `over` sub
                   , s' <- slotVars `over` sub'
                   , asDoW (sub, s) == asDoW (sub', s')
                   ]
  where
    subs  = filter (not . isFixed) ss

-- | 第3学年DQ2に必修はいれない
cond12 ss = (-&&&-) [ neg q
                    | sub <- subs
                    , asYear sub == Y3 && asSeason sub == Spring && required sub
                    , q <- quarterVars `over` sub
                    ]
  where
    subs  = filter (not . isFixed) ss

defaultRules :: [[Subject] -> BoolForm]
defaultRules = [cond1, cond2, cond3, cond4, cond5, cond6, cond7, cond8, cond9, cond10, cond11, cond12]

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
    assignTable :: [Subject] -> [Int] -> TimeTable
    assignTable subs ans = table
      where
        x = filter (0 <) . (take (length subs * bitsForSubject)) $ ans
        comp (p1, s1) (p2, s2) = case compare (target s1) (target s2) of { EQ -> compare p1 p2; x -> x }
        table = sortBy comp $ map (\s -> (asEntry (s, x), s)) subs
  let
    printer :: [Subject] -> [Int] -> IO ()
    printer subs ans = do
        forM_ [Y1 .. Y4] $ \y -> do
          putStrLn $ "### " ++ show y
          forM_ (assignTable subs ans) $ \(e, s) -> do
            when (asYear e == y) $ do
              putStr $ printf "%s: %-24s" (show (asSlot e)) (labelOf s)
              putStrLn . ("\t" ++) . intercalate ", " $ lecturersOf s
  case os of
    ("-i":_) | elem "B" os -> do
      printer subjectsInAutomn . read =<< getContents
    ("-i":_) -> do
      printer subjectsInSpring . read =<< getContents
    ("-d":_) -> do
      putStrLn . asCNFString $ if elem "B" os then r2 else r1
    _ -> do
      case map (SAT.satisfiable (:) . asList) [r1, r2] of
        [[], _] -> putStrLn "can't solve Spring constraints"
        [_, []] -> putStrLn "can't solve Autumn constraints"
        [s:_, a:_] -> do
          let table = concat [ assignTable sub ans
                             | sub <- [subjectsInSpring, subjectsInAutomn]
                             | ans <- [s, a]
                             ]
          forM_ [(Spring, subjectsInSpring, r1, s), (Autumn, subjectsInAutomn, r2, a)] $ \(ssn, subs, cnf, ans) -> do 
            putStr $ "-------- " ++ if ssn == Spring then "春学期" else "秋学期"
            putStrLn $ "; " ++ show (numberOfVariables cnf, numberOfClauses cnf)
            printer subs ans
          -- toLatexTable p table
          withFile "timetable-assign.tex" WriteMode $ toLatex dataName table
          dumpReport table      -- summary report

toLatex :: String -> TimeTable -> Handle -> IO ()
toLatex dataName table h = do
  hPutStrLn h . printf "\\newcommand{\\versionID}{%s (%s)}" dataName =<< currentTimeString
  forM_ tags $ \(e@(y, q, s), k) -> do -- TimeTable == [((Year, Quarter, Slot), Subject)]
    let firstHalf = elem q [Q1, Q3]
    case find ((e ==) . fst) table of
      Just (_, sub) -> do
        let name = labelOf sub
        let lecs' = intercalate "," $ lecturersOf sub
        let lecs = if 5 < length lecs' then "\\tiny " ++ lecs' else lecs'
        case (required sub, atComputerRoom sub) of
          (True , True) -> hPutStr h $ printf "\\newcommand{\\%sSub}{\\cellcolor{blue!10}\\textcolor{red}{\\textbf{%s}}}" k name
          (True , False) | firstHalf -> hPutStr h $ printf "\\newcommand{\\%sSub}{\\textcolor{red}{\\textbf{%s}}}" k name
          (True , False) | not firstHalf -> hPutStr h $ printf "\\newcommand{\\%sSub}{\\cellcolor{black!5}\\textcolor{red}{\\textbf{%s}}}" k name
          (False, True) -> hPutStr h $ printf "\\newcommand{\\%sSub}{\\cellcolor{blue!10}%s}" k name
          (False, False) | firstHalf -> hPutStr h $ printf "\\newcommand{\\%sSub}{%s}" k name
          (False, False) | not firstHalf -> hPutStr h $ printf "\\newcommand{\\%sSub}{\\cellcolor{black!5}%s}" k name
          _ -> putStrLn $ "unhandled pattern: " ++ show (labelOf sub) ++ " @ " ++ show q
        if firstHalf
          then hPutStrLn h $ printf "\\newcommand{\\%sLec}{\\footnotesize %s}" k lecs
          else hPutStrLn h $ printf "\\newcommand{\\%sLec}{\\cellcolor{black!5}\\footnotesize %s}" k lecs
      _ | follwingCell e -> do
        hPutStr h $ printf "\\newcommand{\\%sSub}{\\cellcolor{blue!10}\\hfil↑\\hfil}" k
        if firstHalf
          then hPutStrLn h $ printf "\\newcommand{\\%sLec}{}" k
          else hPutStrLn h $ printf "\\newcommand{\\%sLec}{\\cellcolor{black!5}}" k
      _ | firstHalf -> do
        hPutStr h $ printf "\\newcommand{\\%sSub}{}" k
        hPutStrLn h $ printf "\\newcommand{\\%sLec}{}" k
      _ -> do
        hPutStr h $ printf "\\newcommand{\\%sSub}{\\cellcolor{black!5}}" k
        hPutStrLn h $ printf "\\newcommand{\\%sLec}{\\cellcolor{black!5}}" k
  where
    follwingCell (y, q, s@(Slot d h))
      | elem (asHour s) [H1, H3] = False
      | Just (_, sub) <- find ((k' ==) . fst) table = Nothing /= isLong sub && atComputerRoom sub
      | elem (asHour s) [H2, H4] = False
      | Just (_, sub) <- find ((k'' ==) . fst) table = Just 3 == isLong sub  && atComputerRoom sub
      | otherwise = False
      where
        k' = (y, q, Slot d (pred h))
        k'' = (y, q, Slot d (pred (pred h)))
    tags = [ ( (y, q, Slot d h) , (printf "%s%s%s%s" (yp y) (qp q) (show d) (hp h)) :: String)
           | y <- [minBound :: Year .. maxBound]
           , q <- [minBound :: Quarter .. maxBound]
           , d <- [minBound :: DoW .. maxBound]
           , h <- [minBound :: Hour .. maxBound]
           ]
    yp :: Year -> String
    yp Y1 = "Yone"
    yp Y2 = "Ytwo"
    yp Y3 = "Ythr"
    yp Y4 = "Yfou"
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

toLatexTable :: String -> IO ()
toLatexTable p = do
  forM_ (allItems :: [DoW]) $ \d -> do
    forM_ (allItems :: [Hour]) $ \s -> do
      putStr $ "&" ++ show (fromEnum s + 1) ++ "&"
      forM_ (allItems :: [Year]) $ \y -> do
        forM_ (allItems :: [Quarter]) $ \q -> do
          putStr ((printf "\\%s%s%s%sSub&" (show y) (show q) (show d) (show s)) :: String)
          putStr ((printf "\\%s%s%s%sLec" (show y) (show q) (show d) (show s)) :: String)
          if q == maxBound && y == Y1 then putStrLn "\\\\\\hline" else putStr "&"

currentTimeString :: IO String
currentTimeString = do
  t <- utcToLocalTime <$> (getTimeZone =<< getCurrentTime) <*> getCurrentTime
  return $ formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" t

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

