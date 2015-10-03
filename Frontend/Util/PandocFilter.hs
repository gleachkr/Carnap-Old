import Text.Pandoc.JSON

behead :: Block -> Block
behead (CodeBlock (id,classes,_) xs) 
    | "folproof" `elem` classes = RawBlock (Format "HTML") $ 
                                    "<div id=\"" ++ id ++"\"><textarea class=\"lined FOLproofbox " ++ unwords classes ++ "\">" ++ 
                                     xs ++ 
                                    "</textarea></div>"
    | "slproof" `elem` classes = RawBlock (Format "HTML") $ 
                                    "<div id=\"" ++ id ++"\"><textarea class=\"lined SLproofbox " ++ unwords classes ++ "\">" ++ 
                                     xs ++ 
                                    "</textarea></div>"
behead x = x

main :: IO ()
main = toJSONFilter behead
