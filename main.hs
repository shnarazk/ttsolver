module Main where
import Timetable

subjects :: [Subject]
subjects = canonize
  [
    -- 科目名 時期 必須 担当 連続開講 前提科目 同時開講科目 演習室 表示順序
    Sub "体育" (F Y1 Q1 Mon H1)	True 1 [] [] False ["先生A"] 5
  , Sub "国語" (S Y2 Spring) 	True 1 [] [] False ["先生B"] 1
  , Sub "算数" (S Y3 Spring)	True 1 [] [] False ["教師C"] 2
  , Sub "理科" (S Y2 Spring)	True 1 [] [] False ["先生B", "教師C"] 3
  , Sub "社会" (S Y3 Autumn)	True 1 [] [] False ["教師C"] 4
  ]

makerule x = (-&&&-) $ map ($ x) defaultRules

main = runSolver "sample data" makerule subjects
