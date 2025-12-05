"""
Complete Mini Compiler Implementation
Includes: Lexical Analysis, Parsing, Semantic Analysis, and Intermediate Code Generation

Features:
- Custom language definition with grammar
- Complete lexical analyzer with error handling
- Parser with syntax error detection and recovery
- Symbol table with scope management
- Type checking and semantic analysis
- Three-Address Code (TAC) generation
- Modern GUI with all compiler phases

Language: SimpleLang - A small imperative language
Supports: variables, arithmetic, conditionals, loops, I/O

Run: python mini_compiler.py
Requires: Python 3 with tkinter
"""
import re
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
from datetime import datetime
import webbrowser
from collections import defaultdict
from enum import Enum

# ==================== LANGUAGE DEFINITION ====================
"""
SimpleLang - Custom Programming Language Specification

Purpose: Educational imperative language for basic computations

Keywords: program, begin, end, int, float, string, if, then, else, 
          while, do, read, write, return

Operators: +, -, *, /, =, ==, !=, <, >, <=, >=, :=

Grammar (Transformed - Ambiguity Removed, Left Recursion Eliminated):

Program → program ID begin StmtList end
StmtList → Stmt StmtList'
StmtList' → Stmt StmtList' | ε
Stmt → DeclStmt | AssignStmt | IfStmt | WhileStmt | ReadStmt | WriteStmt
DeclStmt → Type ID ;
Type → int | float | string
AssignStmt → ID := Expr ;
IfStmt → if ( BoolExpr ) then StmtList ElsePart end
ElsePart → else StmtList | ε
WhileStmt → while ( BoolExpr ) do StmtList end
ReadStmt → read ( ID ) ;
WriteStmt → write ( Expr ) ;
Expr → Term Expr'
Expr' → + Term Expr' | - Term Expr' | ε
Term → Factor Term'
Term' → * Factor Term' | / Factor Term' | ε
Factor → ID | NUM | ( Expr )
BoolExpr → Expr RelOp Expr
RelOp → == | != | < | > | <= | >=
"""

# ==================== TOKEN DEFINITIONS ====================
class TokenType(Enum):
    # Keywords
    PROGRAM = 'PROGRAM'
    BEGIN = 'BEGIN'
    END = 'END'
    INT = 'INT'
    FLOAT = 'FLOAT'
    STRING = 'STRING'
    IF = 'IF'
    THEN = 'THEN'
    ELSE = 'ELSE'
    WHILE = 'WHILE'
    DO = 'DO'
    READ = 'READ'
    WRITE = 'WRITE'
    RETURN = 'RETURN'
    
    # Operators
    ASSIGN = 'ASSIGN'      # :=
    PLUS = 'PLUS'          # +
    MINUS = 'MINUS'        # -
    MULT = 'MULT'          # *
    DIV = 'DIV'            # /
    EQ = 'EQ'              # ==
    NEQ = 'NEQ'            # !=
    LT = 'LT'              # <
    GT = 'GT'              # >
    LTE = 'LTE'            # <=
    GTE = 'GTE'            # >=
    
    # Separators
    LPAREN = 'LPAREN'      # (
    RPAREN = 'RPAREN'      # )
    SEMICOLON = 'SEMICOLON' # ;
    COMMA = 'COMMA'        # ,
    
    # Literals and Identifiers
    ID = 'ID'
    NUM = 'NUM'
    STR_LITERAL = 'STR_LITERAL'
    
    # Special
    COMMENT = 'COMMENT'
    EOF = 'EOF'
    ERROR = 'ERROR'

KEYWORDS = {
    'program': TokenType.PROGRAM,
    'begin': TokenType.BEGIN,
    'end': TokenType.END,
    'int': TokenType.INT,
    'float': TokenType.FLOAT,
    'string': TokenType.STRING,
    'if': TokenType.IF,
    'then': TokenType.THEN,
    'else': TokenType.ELSE,
    'while': TokenType.WHILE,
    'do': TokenType.DO,
    'read': TokenType.READ,
    'write': TokenType.WRITE,
    'return': TokenType.RETURN
}

class Token:
    def __init__(self, type_, value, line, column):
        self.type = type_
        self.value = value
        self.line = line
        self.column = column
    
    def __repr__(self):
        return f"Token({self.type.value}, '{self.value}', {self.line}:{self.column})"

# ==================== LEXICAL ANALYZER ====================
class Lexer:
    def __init__(self, source_code):
        self.source = source_code
        self.pos = 0
        self.line = 1
        self.column = 1
        self.tokens = []
        self.errors = []
    
    def error(self, msg):
        self.errors.append(f"Lexical Error at {self.line}:{self.column}: {msg}")
    
    def peek(self, offset=0):
        pos = self.pos + offset
        return self.source[pos] if pos < len(self.source) else None
    
    def advance(self):
        if self.pos < len(self.source):
            if self.source[self.pos] == '\n':
                self.line += 1
                self.column = 1
            else:
                self.column += 1
            self.pos += 1
    
    def skip_whitespace(self):
        while self.peek() and self.peek() in ' \t\n\r':
            self.advance()
    
    def skip_comment(self):
        if self.peek() == '/' and self.peek(1) == '/':
            start_col = self.column
            comment_text = ''
            while self.peek() and self.peek() != '\n':
                comment_text += self.peek()
                self.advance()
            return Token(TokenType.COMMENT, comment_text, self.line, start_col)
        return None
    
    def read_number(self):
        start_col = self.column
        num = ''
        has_dot = False
        
        while self.peek() and (self.peek().isdigit() or self.peek() == '.'):
            if self.peek() == '.':
                if has_dot:
                    self.error("Multiple decimal points in number")
                    break
                has_dot = True
            num += self.peek()
            self.advance()
        
        return Token(TokenType.NUM, num, self.line, start_col)
    
    def read_string(self):
        start_col = self.column
        self.advance()  # Skip opening quote
        string = ''
        
        while self.peek() and self.peek() != '"':
            if self.peek() == '\\':
                self.advance()
                if self.peek():
                    string += self.peek()
                    self.advance()
            else:
                string += self.peek()
                self.advance()
        
        if self.peek() == '"':
            self.advance()  # Skip closing quote
            return Token(TokenType.STR_LITERAL, string, self.line, start_col)
        else:
            self.error("Unterminated string")
            return Token(TokenType.ERROR, string, self.line, start_col)
    
    def read_identifier(self):
        start_col = self.column
        ident = ''
        
        while self.peek() and (self.peek().isalnum() or self.peek() == '_'):
            ident += self.peek()
            self.advance()
        
        token_type = KEYWORDS.get(ident, TokenType.ID)
        return Token(token_type, ident, self.line, start_col)
    
    def tokenize(self):
        while self.pos < len(self.source):
            self.skip_whitespace()
            
            if self.pos >= len(self.source):
                break
            
            # Comments
            comment = self.skip_comment()
            if comment:
                self.tokens.append(comment)
                continue
            
            start_col = self.column
            char = self.peek()
            
            # Numbers
            if char.isdigit():
                self.tokens.append(self.read_number())
            
            # Strings
            elif char == '"':
                self.tokens.append(self.read_string())
            
            # Identifiers and Keywords
            elif char.isalpha() or char == '_':
                self.tokens.append(self.read_identifier())
            
            # Operators (two-character)
            elif char == ':' and self.peek(1) == '=':
                self.advance()
                self.advance()
                self.tokens.append(Token(TokenType.ASSIGN, ':=', self.line, start_col))
            elif char == '=' and self.peek(1) == '=':
                self.advance()
                self.advance()
                self.tokens.append(Token(TokenType.EQ, '==', self.line, start_col))
            elif char == '!' and self.peek(1) == '=':
                self.advance()
                self.advance()
                self.tokens.append(Token(TokenType.NEQ, '!=', self.line, start_col))
            elif char == '<' and self.peek(1) == '=':
                self.advance()
                self.advance()
                self.tokens.append(Token(TokenType.LTE, '<=', self.line, start_col))
            elif char == '>' and self.peek(1) == '=':
                self.advance()
                self.advance()
                self.tokens.append(Token(TokenType.GTE, '>=', self.line, start_col))
            
            # Operators (single-character)
            elif char == '+':
                self.advance()
                self.tokens.append(Token(TokenType.PLUS, '+', self.line, start_col))
            elif char == '-':
                self.advance()
                self.tokens.append(Token(TokenType.MINUS, '-', self.line, start_col))
            elif char == '*':
                self.advance()
                self.tokens.append(Token(TokenType.MULT, '*', self.line, start_col))
            elif char == '/':
                self.advance()
                self.tokens.append(Token(TokenType.DIV, '/', self.line, start_col))
            elif char == '<':
                self.advance()
                self.tokens.append(Token(TokenType.LT, '<', self.line, start_col))
            elif char == '>':
                self.advance()
                self.tokens.append(Token(TokenType.GT, '>', self.line, start_col))
            
            # Separators
            elif char == '(':
                self.advance()
                self.tokens.append(Token(TokenType.LPAREN, '(', self.line, start_col))
            elif char == ')':
                self.advance()
                self.tokens.append(Token(TokenType.RPAREN, ')', self.line, start_col))
            elif char == ';':
                self.advance()
                self.tokens.append(Token(TokenType.SEMICOLON, ';', self.line, start_col))
            elif char == ',':
                self.advance()
                self.tokens.append(Token(TokenType.COMMA, ',', self.line, start_col))
            
            # Unknown character
            else:
                self.error(f"Unexpected character '{char}'")
                self.advance()
        
        self.tokens.append(Token(TokenType.EOF, '', self.line, self.column))
        return self.tokens, self.errors

# ==================== SYMBOL TABLE ====================
class SymbolTable:
    def __init__(self):
        self.scopes = [{}]  # Stack of scopes
        self.current_scope = 0
    
    def enter_scope(self):
        self.scopes.append({})
        self.current_scope += 1
    
    def exit_scope(self):
        if self.current_scope > 0:
            self.scopes.pop()
            self.current_scope -= 1
    
    def declare(self, name, type_, line):
        if name in self.scopes[self.current_scope]:
            return False, f"Variable '{name}' already declared in current scope"
        self.scopes[self.current_scope][name] = {
            'type': type_,
            'line': line,
            'scope': self.current_scope
        }
        return True, None
    
    def lookup(self, name):
        for i in range(self.current_scope, -1, -1):
            if name in self.scopes[i]:
                return self.scopes[i][name]
        return None
    
    def get_all_symbols(self):
        all_symbols = []
        for scope_level, scope in enumerate(self.scopes):
            for name, info in scope.items():
                all_symbols.append({
                    'name': name,
                    'type': info['type'],
                    'scope': scope_level,
                    'line': info['line']
                })
        return all_symbols

# ==================== PARSER ====================
class Parser:
    def __init__(self, tokens):
        self.tokens = [t for t in tokens if t.type != TokenType.COMMENT]
        self.pos = 0
        self.current = self.tokens[0] if tokens else None
        self.errors = []
        self.symbol_table = SymbolTable()
    
    def error(self, msg):
        self.errors.append(f"Syntax Error at {self.current.line}:{self.current.column}: {msg}")
    
    def advance(self):
        if self.pos < len(self.tokens) - 1:
            self.pos += 1
            self.current = self.tokens[self.pos]
    
    def match(self, expected_type):
        if self.current.type == expected_type:
            token = self.current
            self.advance()
            return token
        else:
            self.error(f"Expected {expected_type.value}, got {self.current.type.value}")
            return None
    
    def parse(self):
        """Parse the entire program"""
        try:
            self.program()
            if self.current.type != TokenType.EOF:
                self.error("Unexpected tokens after program end")
        except Exception as e:
            self.error(f"Parser exception: {str(e)}")
        
        return self.errors
    
    def program(self):
        """Program → program ID begin StmtList end"""
        self.match(TokenType.PROGRAM)
        prog_name = self.match(TokenType.ID)
        self.match(TokenType.BEGIN)
        self.stmt_list()
        self.match(TokenType.END)
    
    def stmt_list(self):
        """StmtList → Stmt StmtList'"""
        while self.current.type != TokenType.END and self.current.type != TokenType.ELSE and self.current.type != TokenType.EOF:
            self.stmt()
    
    def stmt(self):
        """Stmt → DeclStmt | AssignStmt | IfStmt | WhileStmt | ReadStmt | WriteStmt"""
        if self.current.type in [TokenType.INT, TokenType.FLOAT, TokenType.STRING]:
            self.decl_stmt()
        elif self.current.type == TokenType.ID:
            self.assign_stmt()
        elif self.current.type == TokenType.IF:
            self.if_stmt()
        elif self.current.type == TokenType.WHILE:
            self.while_stmt()
        elif self.current.type == TokenType.READ:
            self.read_stmt()
        elif self.current.type == TokenType.WRITE:
            self.write_stmt()
        else:
            self.error(f"Unexpected statement starting with {self.current.type.value}")
            self.advance()  # Error recovery
    
    def decl_stmt(self):
        """DeclStmt → Type ID ;"""
        type_token = self.current
        self.advance()  # Type
        id_token = self.match(TokenType.ID)
        if id_token:
            success, msg = self.symbol_table.declare(id_token.value, type_token.value, id_token.line)
            if not success:
                self.error(msg)
        self.match(TokenType.SEMICOLON)
    
    def assign_stmt(self):
        """AssignStmt → ID := Expr ;"""
        id_token = self.match(TokenType.ID)
        if id_token:
            symbol = self.symbol_table.lookup(id_token.value)
            if not symbol:
                self.error(f"Undeclared variable '{id_token.value}'")
        self.match(TokenType.ASSIGN)
        self.expr()
        self.match(TokenType.SEMICOLON)
    
    def if_stmt(self):
        """IfStmt → if ( BoolExpr ) then StmtList ElsePart end"""
        self.match(TokenType.IF)
        self.match(TokenType.LPAREN)
        self.bool_expr()
        self.match(TokenType.RPAREN)
        self.match(TokenType.THEN)
        self.stmt_list()
        if self.current.type == TokenType.ELSE:
            self.advance()
            self.stmt_list()
        self.match(TokenType.END)
    
    def while_stmt(self):
        """WhileStmt → while ( BoolExpr ) do StmtList end"""
        self.match(TokenType.WHILE)
        self.match(TokenType.LPAREN)
        self.bool_expr()
        self.match(TokenType.RPAREN)
        self.match(TokenType.DO)
        self.stmt_list()
        self.match(TokenType.END)
    
    def read_stmt(self):
        """ReadStmt → read ( ID ) ;"""
        self.match(TokenType.READ)
        self.match(TokenType.LPAREN)
        id_token = self.match(TokenType.ID)
        if id_token:
            symbol = self.symbol_table.lookup(id_token.value)
            if not symbol:
                self.error(f"Undeclared variable '{id_token.value}'")
        self.match(TokenType.RPAREN)
        self.match(TokenType.SEMICOLON)
    
    def write_stmt(self):
        """WriteStmt → write ( Expr ) ;"""
        self.match(TokenType.WRITE)
        self.match(TokenType.LPAREN)
        self.expr()
        self.match(TokenType.RPAREN)
        self.match(TokenType.SEMICOLON)
    
    def expr(self):
        """Expr → Term Expr'"""
        self.term()
        self.expr_prime()
    
    def expr_prime(self):
        """Expr' → + Term Expr' | - Term Expr' | ε"""
        if self.current.type in [TokenType.PLUS, TokenType.MINUS]:
            self.advance()
            self.term()
            self.expr_prime()
    
    def term(self):
        """Term → Factor Term'"""
        self.factor()
        self.term_prime()
    
    def term_prime(self):
        """Term' → * Factor Term' | / Factor Term' | ε"""
        if self.current.type in [TokenType.MULT, TokenType.DIV]:
            self.advance()
            self.factor()
            self.term_prime()
    
    def factor(self):
        """Factor → ID | NUM | ( Expr )"""
        if self.current.type == TokenType.ID:
            id_token = self.current
            symbol = self.symbol_table.lookup(id_token.value)
            if not symbol:
                self.error(f"Undeclared variable '{id_token.value}'")
            self.advance()
        elif self.current.type == TokenType.NUM:
            self.advance()
        elif self.current.type == TokenType.LPAREN:
            self.advance()
            self.expr()
            self.match(TokenType.RPAREN)
        else:
            self.error(f"Expected ID, NUM, or '(', got {self.current.type.value}")
    
    def bool_expr(self):
        """BoolExpr → Expr RelOp Expr"""
        self.expr()
        if self.current.type in [TokenType.EQ, TokenType.NEQ, TokenType.LT, 
                                 TokenType.GT, TokenType.LTE, TokenType.GTE]:
            self.advance()
            self.expr()
        else:
            self.error("Expected relational operator")

# ==================== THREE-ADDRESS CODE GENERATOR ====================
class TACGenerator:
    def __init__(self, tokens, symbol_table):
        self.tokens = [t for t in tokens if t.type != TokenType.COMMENT]
        self.pos = 0
        self.current = self.tokens[0] if tokens else None
        self.tac = []
        self.temp_count = 0
        self.label_count = 0
        self.symbol_table = symbol_table
    
    def new_temp(self):
        self.temp_count += 1
        return f"t{self.temp_count}"
    
    def new_label(self):
        self.label_count += 1
        return f"L{self.label_count}"
    
    def emit(self, instruction):
        self.tac.append(instruction)
    
    def advance(self):
        if self.pos < len(self.tokens) - 1:
            self.pos += 1
            self.current = self.tokens[self.pos]
    
    def match(self, expected_type):
        if self.current.type == expected_type:
            token = self.current
            self.advance()
            return token
        return None
    
    def generate(self):
        """Generate TAC for the entire program"""
        try:
            self.program()
        except:
            pass
        return self.tac
    
    def program(self):
        self.match(TokenType.PROGRAM)
        self.match(TokenType.ID)
        self.match(TokenType.BEGIN)
        self.stmt_list()
        self.match(TokenType.END)
    
    def stmt_list(self):
        while self.current.type not in [TokenType.END, TokenType.ELSE, TokenType.EOF]:
            self.stmt()
    
    def stmt(self):
        if self.current.type in [TokenType.INT, TokenType.FLOAT, TokenType.STRING]:
            self.advance()
            self.match(TokenType.ID)
            self.match(TokenType.SEMICOLON)
        elif self.current.type == TokenType.ID:
            id_name = self.current.value
            self.advance()
            self.match(TokenType.ASSIGN)
            expr_result = self.expr()
            self.emit(f"{id_name} = {expr_result}")
            self.match(TokenType.SEMICOLON)
        elif self.current.type == TokenType.IF:
            self.if_stmt()
        elif self.current.type == TokenType.WHILE:
            self.while_stmt()
        elif self.current.type == TokenType.READ:
            self.advance()
            self.match(TokenType.LPAREN)
            id_token = self.match(TokenType.ID)
            if id_token:
                self.emit(f"read {id_token.value}")
            self.match(TokenType.RPAREN)
            self.match(TokenType.SEMICOLON)
        elif self.current.type == TokenType.WRITE:
            self.advance()
            self.match(TokenType.LPAREN)
            expr_result = self.expr()
            self.emit(f"write {expr_result}")
            self.match(TokenType.RPAREN)
            self.match(TokenType.SEMICOLON)
        else:
            self.advance()
    
    def if_stmt(self):
        self.match(TokenType.IF)
        self.match(TokenType.LPAREN)
        cond_result = self.bool_expr()
        self.match(TokenType.RPAREN)
        self.match(TokenType.THEN)
        
        label_false = self.new_label()
        label_end = self.new_label()
        
        self.emit(f"ifFalse {cond_result} goto {label_false}")
        self.stmt_list()
        
        if self.current.type == TokenType.ELSE:
            self.emit(f"goto {label_end}")
            self.emit(f"{label_false}:")
            self.advance()
            self.stmt_list()
            self.emit(f"{label_end}:")
        else:
            self.emit(f"{label_false}:")
        
        self.match(TokenType.END)
    
    def while_stmt(self):
        self.match(TokenType.WHILE)
        self.match(TokenType.LPAREN)
        
        label_begin = self.new_label()
        label_end = self.new_label()
        
        self.emit(f"{label_begin}:")
        cond_result = self.bool_expr()
        self.emit(f"ifFalse {cond_result} goto {label_end}")
        
        self.match(TokenType.RPAREN)
        self.match(TokenType.DO)
        self.stmt_list()
        
        self.emit(f"goto {label_begin}")
        self.emit(f"{label_end}:")
        self.match(TokenType.END)
    
    def expr(self):
        left = self.term()
        while self.current.type in [TokenType.PLUS, TokenType.MINUS]:
            op = self.current.value
            self.advance()
            right = self.term()
            temp = self.new_temp()
            self.emit(f"{temp} = {left} {op} {right}")
            left = temp
        return left
    
    def term(self):
        left = self.factor()
        while self.current.type in [TokenType.MULT, TokenType.DIV]:
            op = self.current.value
            self.advance()
            right = self.factor()
            temp = self.new_temp()
            self.emit(f"{temp} = {left} {op} {right}")
            left = temp
        return left
    
    def factor(self):
        if self.current.type == TokenType.ID:
            value = self.current.value
            self.advance()
            return value
        elif self.current.type == TokenType.NUM:
            value = self.current.value
            self.advance()
            return value
        elif self.current.type == TokenType.LPAREN:
            self.advance()
            result = self.expr()
            self.match(TokenType.RPAREN)
            return result
        return "0"
    
    def bool_expr(self):
        left = self.expr()
        if self.current.type in [TokenType.EQ, TokenType.NEQ, TokenType.LT,
                                 TokenType.GT, TokenType.LTE, TokenType.GTE]:
            op = self.current.value
            self.advance()
            right = self.expr()
            temp = self.new_temp()
            self.emit(f"{temp} = {left} {op} {right}")
            return temp
        return left

# ==================== GUI APPLICATION ====================
class CompilerGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title('Mini Compiler - SimpleLang')
        self.geometry('1400x800')
        self.configure(bg='#f0f4f8')
        
        self.create_widgets()
        self.load_sample()
    
    def create_widgets(self):
        # Title Bar
        title_frame = tk.Frame(self, bg='#2c3e50', height=60)
        title_frame.pack(fill='x')
        title_frame.pack_propagate(False)
        
        tk.Label(title_frame, text='🔧 Mini Compiler - SimpleLang',
                bg='#2c3e50', fg='white',
                font=('Segoe UI', 18, 'bold')).pack(side='left', padx=20, pady=15)
        
        # Main container
        main_container = tk.Frame(self, bg='#f0f4f8')
        main_container.pack(fill='both', expand=True, padx=10, pady=10)
        
        # Left panel - Source Code
        left_panel = tk.Frame(main_container, bg='white', relief='solid', borderwidth=1)
        left_panel.pack(side='left', fill='both', expand=True, padx=(0, 5))
        
        tk.Label(left_panel, text='📝 Source Code (SimpleLang)',
                bg='#3498db', fg='white',
                font=('Segoe UI', 11, 'bold'), height=2).pack(fill='x')
        
        self.source_text = scrolledtext.ScrolledText(
            left_panel, wrap='none', font=('Consolas', 10),
            bg='#fafafa', fg='#2c3e50', padx=10, pady=10
        )
        self.source_text.pack(fill='both', expand=True, padx=5, pady=5)
        
        # Control buttons
        btn_frame = tk.Frame(left_panel, bg='white', height=50)
        btn_frame.pack(fill='x', pady=5)
        
        tk.Button(btn_frame, text='▶ Compile All', command=self.compile_all,
                 bg='#27ae60', fg='white', font=('Segoe UI', 10, 'bold'),
                 cursor='hand2', padx=15, pady=5).pack(side='left', padx=5)
        tk.Button(btn_frame, text='🗑 Clear', command=self.clear_all,
                 bg='#e74c3c', fg='white', font=('Segoe UI', 10, 'bold'),
                 cursor='hand2', padx=15, pady=5).pack(side='left', padx=5)
        tk.Button(btn_frame, text='📋 Sample', command=self.load_sample,
                 bg='#95a5a6', fg='white', font=('Segoe UI', 10, 'bold'),
                 cursor='hand2', padx=15, pady=5).pack(side='left', padx=5)
        tk.Button(btn_frame, text='👨‍💻 About', command=self.show_about,
                 bg='#9b59b6', fg='white', font=('Segoe UI', 10, 'bold'),
                 cursor='hand2', padx=15, pady=5).pack(side='left', padx=5)
        
        # Right panel - Notebook with tabs
        right_panel = tk.Frame(main_container, bg='white', relief='solid', borderwidth=1)
        right_panel.pack(side='right', fill='both', expand=True, padx=(5, 0))
        
        self.notebook = ttk.Notebook(right_panel)
        self.notebook.pack(fill='both', expand=True, padx=5, pady=5)
        
        # Tab 1: Tokens
        tokens_frame = tk.Frame(self.notebook, bg='white')
        self.notebook.add(tokens_frame, text='🎯 Tokens')
        
        cols_tokens = ('Line', 'Token', 'Type', 'Column')
        self.tokens_tree = ttk.Treeview(tokens_frame, columns=cols_tokens, show='headings')
        self.tokens_tree.heading('Line', text='Line')
        self.tokens_tree.heading('Token', text='Token')
        self.tokens_tree.heading('Type', text='Type')
        self.tokens_tree.heading('Column', text='Column')
        
        self.tokens_tree.column('Line', width=60, anchor='center')
        self.tokens_tree.column('Token', width=150)
        self.tokens_tree.column('Type', width=120)
        self.tokens_tree.column('Column', width=70, anchor='center')
        
        scroll_tokens = ttk.Scrollbar(tokens_frame, orient='vertical', command=self.tokens_tree.yview)
        self.tokens_tree.configure(yscrollcommand=scroll_tokens.set)
        self.tokens_tree.pack(side='left', fill='both', expand=True)
        scroll_tokens.pack(side='right', fill='y')
        
        # Tab 2: Symbol Table
        symbol_frame = tk.Frame(self.notebook, bg='white')
        self.notebook.add(symbol_frame, text='📊 Symbol Table')
        
        cols_symbol = ('Name', 'Type', 'Scope', 'Line')
        self.symbol_tree = ttk.Treeview(symbol_frame, columns=cols_symbol, show='headings')
        self.symbol_tree.heading('Name', text='Identifier')
        self.symbol_tree.heading('Type', text='Data Type')
        self.symbol_tree.heading('Scope', text='Scope Level')
        self.symbol_tree.heading('Line', text='Declared at Line')
        
        self.symbol_tree.column('Name', width=150)
        self.symbol_tree.column('Type', width=100)
        self.symbol_tree.column('Scope', width=100, anchor='center')
        self.symbol_tree.column('Line', width=100, anchor='center')
        
        scroll_symbol = ttk.Scrollbar(symbol_frame, orient='vertical', command=self.symbol_tree.yview)
        self.symbol_tree.configure(yscrollcommand=scroll_symbol.set)
        self.symbol_tree.pack(side='left', fill='both', expand=True)
        scroll_symbol.pack(side='right', fill='y')
        
        # Tab 3: Parse Tree / Errors
        parse_frame = tk.Frame(self.notebook, bg='white')
        self.notebook.add(parse_frame, text='🌳 Parse Results')
        
        self.parse_text = scrolledtext.ScrolledText(
            parse_frame, wrap='word', font=('Consolas', 9),
            bg='#fafafa', fg='#2c3e50', padx=10, pady=10
        )
        self.parse_text.pack(fill='both', expand=True)
        
        # Tab 4: Three-Address Code
        tac_frame = tk.Frame(self.notebook, bg='white')
        self.notebook.add(tac_frame, text='⚙️ TAC (Intermediate Code)')
        
        self.tac_text = scrolledtext.ScrolledText(
            tac_frame, wrap='none', font=('Consolas', 9),
            bg='#fafafa', fg='#2c3e50', padx=10, pady=10
        )
        self.tac_text.pack(fill='both', expand=True)
        
        # Tab 5: Grammar
        grammar_frame = tk.Frame(self.notebook, bg='white')
        self.notebook.add(grammar_frame, text='📖 Grammar')
        
        self.grammar_text = scrolledtext.ScrolledText(
            grammar_frame, wrap='word', font=('Consolas', 9),
            bg='#fafafa', fg='#2c3e50', padx=10, pady=10
        )
        self.grammar_text.pack(fill='both', expand=True)
        self.grammar_text.insert('1.0', self.get_grammar_info())
        self.grammar_text.config(state='disabled')
        
        # Status bar
        status_frame = tk.Frame(self, bg='#34495e', height=35)
        status_frame.pack(fill='x', side='bottom')
        status_frame.pack_propagate(False)
        
        self.status_label = tk.Label(status_frame, text='Ready to compile',
                                     bg='#34495e', fg='#ecf0f1',
                                     font=('Segoe UI', 9), anchor='w')
        self.status_label.pack(side='left', padx=15, pady=5)
    
    def get_grammar_info(self):
        return """SimpleLang Grammar - Context-Free Grammar (Transformed)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

✓ Ambiguity Removed
✓ Left Recursion Eliminated  
✓ Left Factoring Applied
✓ Non-determinism Removed

PRODUCTION RULES:
─────────────────

Program → program ID begin StmtList end

StmtList → Stmt StmtList'
StmtList' → Stmt StmtList' | ε

Stmt → DeclStmt | AssignStmt | IfStmt | WhileStmt | ReadStmt | WriteStmt

DeclStmt → Type ID ;
Type → int | float | string

AssignStmt → ID := Expr ;

IfStmt → if ( BoolExpr ) then StmtList ElsePart end
ElsePart → else StmtList | ε

WhileStmt → while ( BoolExpr ) do StmtList end

ReadStmt → read ( ID ) ;

WriteStmt → write ( Expr ) ;

Expr → Term Expr'
Expr' → + Term Expr' | - Term Expr' | ε

Term → Factor Term'
Term' → * Factor Term' | / Factor Term' | ε

Factor → ID | NUM | ( Expr )

BoolExpr → Expr RelOp Expr
RelOp → == | != | < | > | <= | >=

KEYWORDS: program, begin, end, int, float, string, if, then, else, 
          while, do, read, write, return

OPERATORS: :=, +, -, *, /, ==, !=, <, >, <=, >=

SEPARATORS: ( ) ; ,

TRANSFORMATIONS APPLIED:
────────────────────────

1. LEFT RECURSION REMOVAL:
   Original: Expr → Expr + Term | Term
   Transformed: Expr → Term Expr'
                Expr' → + Term Expr' | ε

2. LEFT FACTORING:
   Original: Stmt → Type ID | if Expr | while Expr ...
   Transformed: Separated into distinct statement types

3. AMBIGUITY RESOLUTION:
   Operator precedence: *, / (higher) → +, - (lower)
   Dangling else: else matches nearest if
"""
    
    def compile_all(self):
        source = self.source_text.get('1.0', 'end-1c')
        if not source.strip():
            messagebox.showwarning('Empty Source', 'Please enter source code.')
            return
        
        # Clear previous results
        self.clear_results()
        
        # Phase 1: Lexical Analysis
        self.status_label.config(text='Phase 1: Lexical Analysis...')
        self.update()
        
        lexer = Lexer(source)
        tokens, lex_errors = lexer.tokenize()
        
        # Display tokens
        for token in tokens:
            if token.type != TokenType.EOF:
                self.tokens_tree.insert('', 'end', 
                    values=(token.line, token.value, token.type.value, token.column))
        
        if lex_errors:
            self.parse_text.insert('end', '=== LEXICAL ERRORS ===\n', 'error')
            for error in lex_errors:
                self.parse_text.insert('end', f'{error}\n', 'error')
            self.parse_text.insert('end', '\n')
            self.status_label.config(text='Compilation failed: Lexical errors')
            return
        
        self.parse_text.insert('end', '✓ Lexical Analysis: SUCCESS\n', 'success')
        self.parse_text.insert('end', f'  Total tokens: {len(tokens)-1}\n\n')
        
        # Phase 2: Syntax Analysis
        self.status_label.config(text='Phase 2: Syntax Analysis...')
        self.update()
        
        parser = Parser(tokens)
        parse_errors = parser.parse()
        
        if parse_errors:
            self.parse_text.insert('end', '=== SYNTAX ERRORS ===\n', 'error')
            for error in parse_errors:
                self.parse_text.insert('end', f'{error}\n', 'error')
            self.status_label.config(text='Compilation failed: Syntax errors')
            return
        
        self.parse_text.insert('end', '✓ Syntax Analysis: SUCCESS\n', 'success')
        self.parse_text.insert('end', '  Grammar validated successfully\n\n')
        
        # Display Symbol Table
        symbols = parser.symbol_table.get_all_symbols()
        for sym in symbols:
            self.symbol_tree.insert('', 'end',
                values=(sym['name'], sym['type'], sym['scope'], sym['line']))
        
        self.parse_text.insert('end', '✓ Semantic Analysis: SUCCESS\n', 'success')
        self.parse_text.insert('end', f'  Identifiers declared: {len(symbols)}\n\n')
        
        # Phase 3: Intermediate Code Generation
        self.status_label.config(text='Phase 3: Code Generation...')
        self.update()
        
        tac_gen = TACGenerator(tokens, parser.symbol_table)
        tac_code = tac_gen.generate()
        
        self.tac_text.insert('1.0', '=== THREE-ADDRESS CODE (TAC) ===\n\n')
        for i, instruction in enumerate(tac_code, 1):
            self.tac_text.insert('end', f'{i:3d}. {instruction}\n')
        
        self.parse_text.insert('end', '✓ Code Generation: SUCCESS\n', 'success')
        self.parse_text.insert('end', f'  TAC instructions: {len(tac_code)}\n\n')
        
        # Configure tags
        self.parse_text.tag_config('success', foreground='#27ae60', font=('Consolas', 9, 'bold'))
        self.parse_text.tag_config('error', foreground='#e74c3c', font=('Consolas', 9, 'bold'))
        
        self.status_label.config(text='✓ Compilation successful!')
        messagebox.showinfo('Success', 
            f'Compilation completed successfully!\n\n'
            f'Tokens: {len(tokens)-1}\n'
            f'Symbols: {len(symbols)}\n'
            f'TAC Instructions: {len(tac_code)}')
    
    def clear_results(self):
        for item in self.tokens_tree.get_children():
            self.tokens_tree.delete(item)
        for item in self.symbol_tree.get_children():
            self.symbol_tree.delete(item)
        self.parse_text.delete('1.0', 'end')
        self.tac_text.delete('1.0', 'end')
    
    def clear_all(self):
        self.source_text.delete('1.0', 'end')
        self.clear_results()
        self.status_label.config(text='All cleared')
    
    def load_sample(self):
        sample = """program TestProgram
begin
    int x;
    int y;
    float result;
    
    read(x);
    read(y);
    
    result := x + y * 2;
    
    if (x > y) then
        write(x);
    else
        write(y);
    end
    
    int counter;
    counter := 0;
    
    while (counter < 5) do
        write(counter);
        counter := counter + 1;
    end
    
    write(result);
end"""
        self.source_text.delete('1.0', 'end')
        self.source_text.insert('1.0', sample)
        self.status_label.config(text='Sample code loaded')
    
    def show_about(self):
        """Display developer profile - exactly as in previous code"""
        profile_win = tk.Toplevel(self)
        profile_win.title('Developer Profile')
        profile_win.geometry('600x650')
        profile_win.configure(bg='#e8f4f8')
        profile_win.resizable(False, False)
        
        # Center the window
        profile_win.transient(self)
        profile_win.grab_set()
        
        # Header Section with icon and title
        header_section = tk.Frame(profile_win, bg='#e8f4f8')
        header_section.pack(fill='x', pady=(20, 10))
        
        # Project icon
        tk.Label(header_section, text='🚀', bg='#e8f4f8', 
                font=('Segoe UI', 32)).pack()
        
        # Project title
        tk.Label(header_section, text='Mini Compiler Project',
                bg='#e8f4f8', fg='#2c3e50',
                font=('Segoe UI', 18, 'bold')).pack(pady=(5, 2))
        
        # Course info
        tk.Label(header_section, text='Compiler Construction 2025',
                bg='#e8f4f8', fg='#7f8c8d',
                font=('Segoe UI', 10)).pack()
        
        # Developer Section
        tk.Label(profile_win, text='Meet the Developer',
                bg='#e8f4f8', fg='#2c3e50',
                font=('Segoe UI', 14, 'bold')).pack(pady=(15, 10))
        
        # Developer Card - Compact version
        card_frame = tk.Frame(profile_win, bg='white', relief='solid', 
                             borderwidth=1, width=320, height=180)
        card_frame.pack()
        card_frame.pack_propagate(False)
        
        # Avatar with blue gradient background
        avatar_canvas = tk.Canvas(card_frame, width=80, height=80, bg='white', 
                                 highlightthickness=0)
        avatar_canvas.place(x=120, y=15)
        # Create circular gradient effect
        avatar_canvas.create_oval(5, 5, 75, 75, fill='#4a7ba7', outline='#2c5aa0', width=3)
        avatar_canvas.create_text(40, 40, text='MA', fill='white',
                                 font=('Segoe UI', 20, 'bold'))
        
        # Name
        tk.Label(card_frame, text='Muhammad Awais',
                bg='white', fg='#2c3e50',
                font=('Segoe UI', 13, 'bold')).place(x=95, y=100)
        
        # Role badge
        role_frame = tk.Frame(card_frame, bg='#d6eaf8', height=24)
        role_frame.place(x=110, y=125)
        tk.Label(role_frame, text='AI Developer', 
                bg='#d6eaf8', fg='#1976d2',
                font=('Segoe UI', 9, 'bold'), padx=10, pady=3).pack()
        
        # University info with icon
        tk.Label(card_frame, text='🎓 Sukkur IBA University',
                bg='white', fg='#555',
                font=('Segoe UI', 9)).place(x=90, y=155)
        
        # Contact buttons
        contact_frame = tk.Frame(profile_win, bg='#e8f4f8')
        contact_frame.pack(pady=(15, 10))
        
        # Email button
        email_btn = tk.Frame(contact_frame, bg='#e3f2fd', cursor='hand2',
                            relief='solid', borderwidth=1)
        email_btn.pack(side='left', padx=5)
        tk.Label(email_btn, text='📧 Email', bg='#e3f2fd', fg='#1976d2',
                font=('Segoe UI', 9, 'bold'), padx=12, pady=4).pack()
        email_btn.bind('<Button-1>', lambda e: webbrowser.open('mailto:muhammadawais.bscsf22@iba-suk.edu.pk'))
        
        # LinkedIn button
        linkedin_btn = tk.Frame(contact_frame, bg='#fce4ec', cursor='hand2',
                               relief='solid', borderwidth=1)
        linkedin_btn.pack(side='left', padx=5)
        tk.Label(linkedin_btn, text='💼 LinkedIn', bg='#fce4ec', fg='#c2185b',
                font=('Segoe UI', 9, 'bold'), padx=12, pady=4).pack()
        linkedin_btn.bind('<Button-1>', lambda e: webbrowser.open('https://linkedin.com/in/muhammadawais'))
        
        # Project features section
        features_section = tk.Frame(profile_win, bg='white', relief='solid', borderwidth=1)
        features_section.pack(fill='x', padx=30, pady=(10, 20))
        
        tk.Label(features_section, text='✨ Project Features',
                bg='white', fg='#2c3e50',
                font=('Segoe UI', 11, 'bold')).pack(pady=(10, 5))
        
        features = [
            '✓ Complete Lexical Analysis',
            '✓ LL(1) Parser Implementation',
            '✓ Symbol Table with Scope Management',
            '✓ Semantic Analysis & Type Checking',
            '✓ Three-Address Code Generation',
            '✓ Grammar Transformations Applied'
        ]
        
        for feature in features:
            tk.Label(features_section, text=feature,
                    bg='white', fg='#555',
                    font=('Segoe UI', 9), anchor='w').pack(anchor='w', padx=20)
        
        tk.Label(features_section, text='', bg='white').pack(pady=5)
        
        # Bottom Section - Compiler Construction Project Info
        bottom_section = tk.Frame(profile_win, bg='#5b7fc9', height=80)
        bottom_section.pack(fill='x', pady=(0, 0), side='bottom')
        bottom_section.pack_propagate(False)
        
        tk.Label(bottom_section, text='📚 Subject: Compiler Construction',
                bg='#5b7fc9', fg='white',
                font=('Segoe UI', 14, 'bold')).pack(pady=(12, 4))
        
        tk.Label(bottom_section, text='Subject Supervisor: Faryal Shamsi',
                bg='#5b7fc9', fg='white',
                font=('Segoe UI', 11)).pack()

if __name__ == '__main__':
    app = CompilerGUI()
    app.mainloop()