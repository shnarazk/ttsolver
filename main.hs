module Main where
import Timetable

subjects :: [Subject]
subjects = canonize
  [
    -- 科目名 時期 必須 担当 連続開講 前提科目 同時開講科目 演習室
    Sub "体育" (F Y1 Q1 Mon H1)	True ["先生A"] 1 [] [] False
  , Sub "国語" (S Y2 Spring) 	True ["先生B"] 1 [] [] False
  , Sub "算数" (S Y3 Spring)	True ["教師C"] 1 [] [] False
  , Sub "理科" (S Y2 Spring)	True ["先生B", "教師C"] 1 [] [] False
  , Sub "社会" (S Y3 Autumn)	True ["教師C"] 1 [] [] False
  ]

makerule x = (-&&&-) $ map ($ x) defaultRules

main = runSolver "sample data" makerule subjects
