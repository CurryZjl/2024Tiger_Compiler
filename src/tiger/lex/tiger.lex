%filenames = "scanner"

 /*
  * Please don't modify the lines above.
  */

 /* You can add lex definitions here. */
 /* TODO: Put your lab2 code here */

%x COMMENT STR IGNORE

%%
 /* reserved words */
"while" {adjust(); return Parser::WHILE;}
"for" {adjust(); return Parser::FOR;}
"to" {adjust(); return Parser::TO;}
"break" {adjust(); return Parser::BREAK;}
"let" {adjust(); return Parser::LET;}
"in" {adjust(); return Parser::IN;}
"end" {adjust(); return Parser::END;}
"function" {adjust(); return Parser::FUNCTION;}
"var" {adjust(); return Parser::VAR;}
"type" {adjust(); return Parser::TYPE;}
"array" {adjust(); return Parser::ARRAY;}
"if" {adjust(); return Parser::IF;}
"then" {adjust(); return Parser::THEN;}
"else" {adjust(); return Parser::ELSE;}
"do" {adjust(); return Parser::DO;}
"of" {adjust(); return Parser::OF;}
"nil" {adjust(); return Parser::NIL;}

 /* punctuation */
"," {adjust(); return Parser::COMMA;}
":" {adjust(); return Parser::COLON;}
";" {adjust(); return Parser::SEMICOLON;}
"(" {adjust(); return Parser::LPAREN;}
")" {adjust(); return Parser::RPAREN;}
"[" {adjust(); return Parser::LBRACK;}
"]" {adjust(); return Parser::RBRACK;}
"{" {adjust(); return Parser::LBRACE;}
"}" {adjust(); return Parser::RBRACE;}
"." {adjust(); return Parser::DOT;}
"+" {adjust(); return Parser::PLUS;}
"-" {adjust(); return Parser::MINUS;}
"*" {adjust(); return Parser::TIMES;}
"/" {adjust(); return Parser::DIVIDE;}
"=" {adjust(); return Parser::EQ;}
"<>" {adjust(); return Parser::NEQ;}
"<" {adjust(); return Parser::LT;}
"<=" {adjust(); return Parser::LE;}
">" {adjust(); return Parser::GT;}
">=" {adjust(); return Parser::GE;}
"&" {adjust(); return Parser::AND;}
"|" {adjust(); return Parser::OR;}
":=" {adjust(); return Parser::ASSIGN;}

 /* ID and INT */
[[:digit:]]+ {adjust(); return Parser::INT;}
[[:alpha:]][[:alnum:]_]* {adjust(); return Parser::ID;}


 /* TODO: Put your lab2 code here */

/* comment */

"/*" {
  adjust();
  comment_level_++;
  begin(StartCondition_::COMMENT);
}

<COMMENT> {
  "/*" {
    adjust();
    comment_level_++;
  }

  "*/" {
    adjust();
    comment_level_--;
    if (comment_level_ == 1)
      begin(StartCondition_::INITIAL);
  }

  \n {
    adjust();
    errormsg_->Newline();
  }

  . {
    adjust();
  }
}

 /* string literal */

\" {
  adjust();
  begin(StartCondition_::STR);
}
<STR> {
  /* 除了双引号和反斜杠之外的字符都收集起来 */
  ([[:print:]]{-}[\"\\]{+}[[:space:]])+ {
    adjustStr();
    string_buf_ += matched();
  }

  \" {
    adjustStr();
    begin(StartCondition_::INITIAL);
    setMatched(string_buf_);
    string_buf_.clear();
    return Parser::STRING;
  }
  
  \\ {
    adjustStr();
    begin(StartCondition_::IGNORE);
  }
}

<IGNORE> {
  "n" {
    adjustStr();
    string_buf_ += "\n";
    begin(StartCondition_::STR);
  }
  
  "t" {
    adjustStr();
    string_buf_ += "\t";
    begin(StartCondition_::STR);
  }

  \\ {
    adjustStr();
    string_buf_ += "\\";
    begin(StartCondition_::STR);
  }

  \" {
    adjustStr();
    string_buf_ += "\"";
    begin(StartCondition_::STR);
  }
 
  [[:digit:]]{3} {
    adjustStr();
    string_buf_ += (char) atoi(matched().data());
    begin(StartCondition_::STR);
  }

  [[:space:]]+\\ {
    adjustStr();
    begin(StartCondition_::STR);
  }

  "^C" {
    adjustStr();
    string_buf_ += (char) 3;
    begin(StartCondition_::STR);
  }
  "^E" {
    adjustStr();
    string_buf_ += (char) 5;
    begin(StartCondition_::STR);
  }
  "^I" {
    adjustStr();
    string_buf_ += (char) 9;
    begin(StartCondition_::STR);
  }
  "^L" {
    adjustStr();
    string_buf_ += (char) 12;
    begin(StartCondition_::STR);
  }
  "^M" {
    adjustStr();
    string_buf_ += (char) 13;
    begin(StartCondition_::STR);
  }
  "^O" {
    adjustStr();
    string_buf_ += (char) 15;
    begin(StartCondition_::STR);
  }
  "^P" {
    adjustStr();
    string_buf_ += (char) 16;
    begin(StartCondition_::STR);
  }
  "^R" {
    adjustStr();
    string_buf_ += (char) 18;
    begin(StartCondition_::STR);
  }
  "^S" {
    adjustStr();
    string_buf_ += (char) 19;
    begin(StartCondition_::STR);
  }
}


 /*
  * skip white space chars.
  * space, tabs and LF
  */
[ \t]+ {adjust();}
\n {adjust(); errormsg_->Newline();}

 /* illegal input */
. {adjust(); errormsg_->Error(errormsg_->tok_pos_, "illegal token");}
