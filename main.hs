module Main where
import Timetable

subjects :: [Subject]
subjects = canonize
  [
    -- 科目名 時期 必須 担当 連続開講 前提科目 同時開講科目 演習室
    Sub "体育" (F Y1 Q1 Mon H1)	True 1 [] [] False  ["先生A"]
  , Sub "国語" (S Y2 Spring) 	True 1 [] [] False ["先生B"]
  , Sub "算数" (S Y3 Spring)	True 1 [] [] False ["教師C"]
  , Sub "理科" (S Y2 Spring)	True 1 [] [] False ["先生B", "教師C"]
  , Sub "社会" (S Y3 Autumn)	True 1 [] [] False ["教師C"]
  ]

makerule x = (-&&&-) $ map ($ x) defaultRules

main = runSolver "sample data" makerule subjects
