{-#LANGUAGE OverlappingInstances #-}
{- Copyright (C) 2015 Jake Ehrlich and Graham Leach-Krouse <gleachkr@ksu.edu>

This file is part of Carnap 

Carnap is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Carnap is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with Carnap. If not, see <http://www.gnu.org/licenses/>.
- -}
module Main (
    main
) where

import Data.Map as M (lookup, foldrWithKey, empty, insert, union,fromList)
import Data.Maybe (catMaybes)
import Data.Time.Clock (getCurrentTime, utctDayTime, utctDay)
import Data.Time.Calendar (toGregorian)
import Data.Time.LocalTime (timeToTimeOfDay)
import Data.List (intercalate)
import Carnap.Core.Data.Rules (Sequent(Sequent))
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (SSequentItem(SeqList))
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftToScheme)
import Carnap.Frontend.Ghcjs.Components.BoxSettings (BoxSettings(..), initSettingsFOL, shortModTable, shortToModTableFOL)
import Carnap.Frontend.Ghcjs.Components.GenShowBox (genShowBox)
import Carnap.Frontend.Ghcjs.Components.KeyCatcher (keyCatcher)
import Carnap.Frontend.Ghcjs.Components.GenHelp (helpPopupQL,helpPopupLogicBookSD)
import Carnap.Frontend.Ghcjs.Components.GenPopup (genPopup)
import Carnap.Frontend.Ghcjs.Components.HelperFunctions (htmlColltoList,saveAs,lineWithDelay)
import Carnap.Languages.Util.ParserTypes (FParser(..))
import Carnap.Languages.FirstOrder.QuantifiedParser (formulaParser)
import Text.Parsec (runParser)
import Text.Parsec.Char (char) 
import Text.Parsec.Combinator (many1,sepBy,sepEndBy1)
import Control.Monad (when)
import GHCJS.DOM.HTMLTextAreaElement (castToHTMLTextAreaElement, htmlTextAreaElementGetValue)
import GHCJS.DOM.HTMLInputElement (castToHTMLInputElement, htmlInputElementGetValue)
import GHCJS.DOM.HTMLElement (htmlElementGetChildren, castToHTMLElement, htmlElementGetInnerHTML, htmlElementSetInnerHTML)
import GHCJS.DOM.Element (elementSetAttribute, elementGetAttribute, elementFocus, elementOnclick)
import GHCJS.DOM.Node (nodeGetChildNodes, nodeGetFirstChild,nodeAppendChild,nodeInsertBefore,nodeGetNextSibling)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.Document (documentGetBody, documentGetElementById, documentCreateElement, documentGetDefaultView, documentGetDocumentURI)
import GHCJS.DOM.DOMWindow (domWindowAlert)
import Network.URI (unEscapeString)
import Control.Monad.Trans (liftIO)

--foreign import javascript unsafe        "document.write($1+'<br/>');" writeNumber :: Int -> IO ()

main = runWebGUI $ \webView -> do  
        enableInspector webView
        Just doc <- webViewGetDomDocument webView
        Just proofDiv <- documentGetElementById doc "proofDiv"
        dv@(Just win) <- documentGetDefaultView doc 
        url <- documentGetDocumentURI doc :: IO String
        let metadata = insert "Url" url M.empty
        let qs = dropWhile (/= '?') url
        let qs' = unEscapeString $ tail qs
        case qs' of
            _:m:qs'' -> case runParser goalList (initState formulaParser) "" qs'' of
                     Left _ -> domWindowAlert win "Sorry, the url supplied is not well-formed"
                     Right ls@((p,c):xs) -> do let mmod = M.lookup m shortModTable
                                               let mmod2 = M.lookup m shortToModTableFOL
                                               mapM_ (goalDiv mmod doc proofDiv) ls
                                               print $ head qs
                                               if head qs' == '0' 
                                                   then genSubmissionDiv doc proofDiv mmod2 metadata 
                                                               [ ("First Name", "First Name")
                                                               , ("Last Name", "Last Name")
                                                               , ("University Email (if possible)", "Email")
                                                               ] 
                                                     --list of defaults and
                                                     --names. could be
                                                     --clearer to make
                                                     --these into pairs.
                                                   else return ()
                                               help <- case mmod of 
                                                         Nothing -> genPopup proofDiv doc helpPopupQL "help"
                                                         Just mod-> case helpMessage $ mod initSettingsFOL of
                                                            Nothing -> genPopup proofDiv doc helpPopupQL "help"
                                                            Just msg -> genPopup proofDiv doc msg "help"
                                               keyCatcher proofDiv $ \kbf k -> do when (k == 63) $ do elementSetAttribute help "style" "display:block" 
                                                                                                      elementFocus help
                                                                                  return (k == 63) --the handler returning true means that the keypress is intercepted
                     k -> domWindowAlert win $ "Unexpected error on query" ++ qs ++ " parsed as " ++ show k
            _ -> domWindowAlert win "sorry, there doesn't appear to be a problem set in the supplied url"
        lineWithDelay
        return ()

genSubmissionDiv doc proofDiv mod metadata fattrs = do lst@(Just sb : Just idiv : mfields) <- mapM (documentCreateElement doc) $ "button":"div": (take (length fattrs) (cycle ["input"]))
                                                       Just body <- documentGetBody doc
                                                       let sb' = castToHTMLElement sb
                                                       let fields = map castToHTMLInputElement $ catMaybes mfields
                                                       htmlElementSetInnerHTML sb' "Save Problems"
                                                       mapM_ (\x -> elementSetAttribute x "type" "text") fields
                                                       elementSetAttribute sb' "style" "display:block;"
                                                       mapM_ (\(x, z) -> elementSetAttribute x "placeholder" (fst z)) (zip fields fattrs)
                                                       mapM_ (\(x, z) -> elementSetAttribute x "name" (snd z)) (zip fields fattrs)
                                                       activateSubmissionButton proofDiv sb mod metadata fields
                                                       nodeAppendChild body (Just idiv)
                                                       mapM_ (nodeAppendChild idiv) mfields
                                                       nodeAppendChild idiv (Just sb)
                                                       return ()

goalDiv mmod doc pd (a,b) = do let a' = Prelude.map liftToScheme a
                               let b' = liftToScheme b
                               mcontainer@(Just cont) <- documentCreateElement doc "div"
                               mfc@(Just fc) <- nodeGetFirstChild pd
                               case mfc of Nothing -> nodeAppendChild pd mcontainer
                                           Just fc -> nodeInsertBefore pd mcontainer mfc
                               case mmod of Nothing -> genShowBox cont doc initSettingsFOL (Sequent [SeqList a'] (SeqList [b']))
                                            Just mod -> genShowBox cont doc (mod initSettingsFOL) (Sequent [SeqList a'] (SeqList [b']))

activateSubmissionButton proofDiv sb mmod md fields = do elementOnclick sb $ 
                                                           liftIO $ do Just proofDivs <- htmlElementGetChildren (castToHTMLElement proofDiv)
                                                                       proofDivList <- htmlColltoList proofDivs
                                                                       proofInfos <- mapM getProofInfo (catMaybes proofDivList)
                                                                       let proofChunks = map (formatInfo mmod) proofInfos
                                                                       extraMD <-  mapM getMDPair fields >>= return . M.fromList
                                                                       ct <- getCurrentTime
                                                                       let secs = utctDayTime ct
                                                                       let (year,month,day) = toGregorian $ utctDay ct
                                                                       let timeMD = fromList [ ("Submission Date", show month ++ "-" ++ show day ++ "-" ++ show year)
                                                                                             , ("UTC Submission Time", show $ timeToTimeOfDay secs)
                                                                                             ]
                                                                       saveAs (formatChunks (md `union` extraMD `union` timeMD) proofChunks) "Hwk.carnap"

--------------------------------------------------------
--Helpers
--------------------------------------------------------

getMDPair input = do v <- htmlInputElementGetValue input
                     n <- elementGetAttribute  input "name"
                     return (n,v)

goalList = goalParser `sepEndBy1` char '.'

goalParser = do prems <- parser formulaParser `sepBy` char ','
                _ <- char ';'
                conc <- parser formulaParser
                return (prems,conc)

getProofInfo proofNode = do Just lw <- nodeGetFirstChild proofNode
                            Just lines <-nodeGetFirstChild lw
                            Just lta <-nodeGetNextSibling lines
                            Just nta <- nodeGetFirstChild lta
                            Just ngoal <- nodeGetNextSibling lw
                            proof <- htmlTextAreaElementGetValue $ castToHTMLTextAreaElement nta
                            goal <- htmlElementGetInnerHTML $ castToHTMLElement ngoal
                            return (goal,proof)

formatInfo mmod (goal, proof) = "```{.folproof " ++ header ++ ".withGoal}\n" 
                                ++ goal ++ "\n" 
                                ++ proof ++ "\n"
                                ++ "```"
    where header = case mmod of Nothing -> ""
                                Just s -> s ++ " "

formatChunks md l = "---\n" 
                  ++ metaDatatoString md
                  ++ "---\n\n\n" 
                  ++ (intercalate "\n\n" l)

metaDatatoString = foldrWithKey (\k v acc -> acc ++ k ++ ": " ++ v ++ "\n" ) ""
