{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Timetable
       (
         module SAT.CNFIO
       , module Timetable.Types
       , module Timetable.Rules
       , runSolver
       )
       where
import Control.Applicative
import Control.Monad
import Data.List
import Data.Ord
import Data.Time
import System.Environment
import System.IO
import Text.Printf
import SAT.CNFIO
import qualified SAT.Solver.SIH4 as SAT
import Timetable.Types
import Timetable.Rules

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
    assignTable subs ans = sort $ map (\s -> (asEntry (s, x), s)) subs
      where x = filter (0 <) . (take (length subs * bitsForSubject)) $ ans
  let
    printer :: [Subject] -> [Int] -> IO ()
    printer subs ans = do
        forM_ [Y1 .. Y4] $ \y -> do
          putStrLn $ "### " ++ show y
          forM_ (assignTable subs ans) $ \(e, s) -> do
            when (asYear e == y) $ do
              putStr $ printf "%s%s: %-24s" (show (asQuarter e)) (show (asSlot e)) (labelOf s)
              putStrLn . ("\t" ++) . intercalate ", " $ lecturersOf s
  case os of
    ("-i":_) | elem "B" os -> do printer subjectsInAutomn . read =<< getContents
    ("-i":_) -> do printer subjectsInSpring . read =<< getContents
    ("-d":_) -> do putStrLn . asCNFString $ if elem "B" os then r2 else r1
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
          withFile "timetable.csv" WriteMode $ toCSV table

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
      | Just (_, sub) <- find ((k' ==) . fst) table = 1 < isLong sub && atComputerRoom sub
      | elem (asHour s) [H2, H4] = False
      | Just (_, sub) <- find ((k'' ==) . fst) table = 2 < isLong sub  && atComputerRoom sub
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

toCSV :: TimeTable -> Handle -> IO ()
toCSV table h = do
  forM_ (sortBy (comparing (csvOrder . snd)) table) $ \(e,s) -> do
    case makeTL table s e of
      Nothing -> return ()
      Just (name, tt) -> do
        -- 科目順序
        hPutStr h $ show $ (csvOrder s)
        hPutStr h ","
        -- 科目名
        hPutStr h $ name
        hPutStr h ","
        -- 単位数
        hPutStr h $ show $ numUnits s
        hPutStr h ","
        -- 必・選
        hPutStr h $ if required s then "必修" else "選択"
        hPutStr h ","
        -- 標準履修年次
        hPutStr h $ show $ fromEnum (asYear s) + 1
        hPutStr h ","
        -- 講義
        hPutStr h $ if not ("演習" `isInfixOf` labelOf s) && not ("実験" `isInfixOf` labelOf s) then "○" else ""
        hPutStr h ","
        -- 演習
        hPutStr h $ if "演習" `isInfixOf` labelOf s then "○" else ""
        hPutStr h ","
        -- 実験
        hPutStr h $ if "実験" `isInfixOf` labelOf s then "○" else ""
        hPutStr h ","
        -- 時間数
        hPutStr h $ tt
        hPutStr h ","
        -- 工業教員免許
        hPutStr h ","
        -- 理科教員免許
        hPutStr h ","
        -- 数学教員免許
        hPutStrLn h ""
    
makeTL :: TimeTable -> Subject -> Entry -> Maybe (String, String)
makeTL table sub e
  | "''" `isInfixOf` (labelOf sub) = Nothing
  | "→" `isPrefixOf` (labelOf sub) = Nothing
  | "→" `isSuffixOf` (labelOf sub) = Just (init name, tt 1 [(asYear e, asQuarter e), (asYear e, succ (asQuarter e))])
  | "'" `isSuffixOf` (labelOf sub) = Just (init name, tt 2 [(asYear e, asQuarter e)])
  | otherwise = Just (name, tt 1 [(asYear e, asQuarter e)])
  where
    name = labelOf sub
    tt :: Int -> [(Year, Quarter)] -> String
    tt n qs = concatMap (\q -> if elem q qs then show n ++ "," else ",") [(y, q) | y <- [Y1 .. Y4], q <- [Q1 .. Q4]]

numUnits :: Subject -> Int
numUnits sub
  | "→" `isSuffixOf` (labelOf sub) = 2
  | "'" `isSuffixOf` (labelOf sub) = 2
  | otherwise = 1
