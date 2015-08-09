import Text.Pandoc.JSON

behead :: Block -> Block
behead (CodeBlock (_,classes,_) xs) 
    | "proof" `elem` classes = RawBlock (Format "HTML") $ 
                                    "<div><textarea class=\"lined proofbox\">" ++ 
                                     xs ++ 
                                    "</textarea></div>"
behead x = x

main :: IO ()
main = toJSONFilter behead
