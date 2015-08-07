import Text.Pandoc.JSON

behead :: Block -> Block
behead (CodeBlock (_,classes,_) xs) 
    | "proof" `elem` classes = RawBlock (Format "HTML") $ 
                                    "<textarea class=\"lined proofbox\">" ++ 
                                     xs ++ 
                                    "</textarea>"
behead x = x

main :: IO ()
main = toJSONFilter behead
