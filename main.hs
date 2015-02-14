module Main where
import Control.Monad
import Data.List
import Timetable

fixed :: TimeTable
fixed = map (\(a, b) -> (a, head (canonize [b]))) $ 
  [
    -- * １年前期
    ((Y1, Q1, Mon, H1), Sub "体育" B1A True ["先生A"] Nothing [] [] False)
  ]

subjects :: [Subject]
subjects = canonize
  [
    -- 科目名 時期 必須 担当 連続開講 前提科目 同時開講科目 演習室
    Sub "国語" B2A True ["先生B"] Nothing [] [] False
  , Sub "算数" B3A True ["教師C"] Nothing [] [] False
  , Sub "理科" B2A True ["先生B", "教師C"] Nothing [] [] False
  , Sub "社会" B3B True ["教師C"] Nothing [] [] False
  ]

makerule x = (-&&&-) $ map ($ x) (snd defaultRules) ++ map (\f -> f x fixed) (fst defaultRules)

main = do
  putStrLn "running ..."
  runSolver makerule fixed subjects
