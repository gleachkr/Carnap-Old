import Text.Pandoc.JSON

behead :: Block -> Block
behead (CodeBlock (id,classes,_) xs) 
    | "proof" `elem` classes = RawBlock (Format "HTML") $ 
                                    "<div id=\"" ++ id ++"\"><textarea class=\"lined proofbox " ++ unwords classes ++ "\">" ++ 
                                     xs ++ 
                                    "</textarea></div>"
behead x = x

main :: IO ()
main = toJSONFilter behead
