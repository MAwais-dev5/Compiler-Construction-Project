"""
Modern Lexical Analyzer with Enhanced GUI
Features:
- Modern gradient design with improved aesthetics
- Comprehensive developer profile with image, social links, and details
- Syntax highlighting in source code
- Enhanced token visualization
- Improved symbol table with export functionality
- Smooth animations and professional styling

Run: python lexical_analyzer_modern.py
Requires: Python 3 with tkinter, Pillow for image handling
"""
import re
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
from tkinter import font as tkfont
from datetime import datetime
import webbrowser

# --- Token definitions ---
KEYWORDS = {
    'if', 'else', 'for', 'while', 'return', 'break', 'continue', 
    'switch', 'case', 'default', 'do', 'goto', 'sizeof', 'typedef'
}
DATATYPES = {
    'int', 'float', 'double', 'char', 'void', 'long', 'short', 
    'signed', 'unsigned', 'bool', 'struct', 'enum', 'union'
}
OPERATORS = {
    '+', '-', '*', '/', '%', '++', '--', '==', '!=', '<', '>', 
    '<=', '>=', '=', '+=', '-=', '*=', '/=', '&&', '||', '!', '&', '|', '^'
}
SEPARATORS = {
    ',', ';', '(', ')', '{', '}', '[', ']', '.', '#', ':'
}

# Regex patterns for tokenization
token_specification = [
    ('COMMENT',     r'//.*|/\*[\s\S]*?\*/'),
    ('HEADER',      r'\#include\s*<[^>]+>'),
    ('STRING',      r'"(\\.|[^"\\])*"'),
    ('CHAR',        r"'(\\.|[^'\\])'"),
    ('NUMBER',      r'\b\d+(?:\.\d+)?[fFlL]?\b'),
    ('ID',          r'\b[A-Za-z_]\w*\b'),
    ('OP',          r'\+\+|--|==|!=|<=|>=|\+=|-=|\*=|/=|&&|\|\||[+\-*/%<>=!&|^]'),
    ('SYMBOL',      r'[(),;{}\[\].:#]'),
    ('NEWLINE',     r'\n'),
    ('SKIP',        r'[ \t]+'),
    ('MISMATCH',    r'.'),
]
master_pattern = re.compile('|'.join('(?P<%s>%s)' % pair for pair in token_specification))

def classify_token(tok):
    if re.fullmatch(r'//.*|/\*[\s\S]*?\*/', tok):
        return 'Comment'
    if re.fullmatch(r'\#include\s*<[^>]+>', tok):
        return 'Header'
    if re.fullmatch(r'"(\\.|[^"\\])*"', tok) or re.fullmatch(r"'(\\.|[^'\\])'", tok):
        return 'String Literal'
    if re.fullmatch(r'\d+(?:\.\d+)?[fFlL]?', tok):
        return 'Number'
    if tok in DATATYPES:
        return 'Data Type'
    if tok in KEYWORDS:
        return 'Keyword'
    if tok in OPERATORS:
        return 'Operator'
    if tok in SEPARATORS:
        return 'Separator'
    if re.fullmatch(r'[A-Za-z_]\w*', tok):
        return 'Identifier'
    return 'Unknown'

def tokenize_line(line):
    tokens = []
    pos = 0
    while pos < len(line):
        m = master_pattern.match(line, pos)
        if not m:
            break
        kind = m.lastgroup
        value = m.group()
        pos = m.end()
        if kind == 'NEWLINE' or kind == 'SKIP':
            continue
        if kind == 'MISMATCH':
            tokens.append((value, 'Unknown'))
        elif kind == 'COMMENT':
            tokens.append((value, 'Comment'))
        elif kind == 'ID':
            typ = classify_token(value)
            tokens.append((value, typ))
        elif kind == 'OP':
            tokens.append((value, 'Operator'))
        elif kind == 'SYMBOL':
            tokens.append((value, 'Separator'))
        elif kind == 'HEADER':
            tokens.append((value, 'Header'))
        else:
            typ = classify_token(value)
            tokens.append((value, typ))
    return tokens


class ModernButton(tk.Canvas):
    """Custom modern button with hover effects"""
    def __init__(self, parent, text, command, bg='#4a90e2', fg='white', width=140, height=35):
        super().__init__(parent, width=width, height=height, bg=parent['bg'], 
                        highlightthickness=0, cursor='hand2')
        self.command = command
        self.bg_color = bg
        self.hover_color = self._lighten_color(bg)
        self.text = text
        self.fg = fg
        self.is_hover = False
        
        self.bind('<Enter>', self._on_enter)
        self.bind('<Leave>', self._on_leave)
        self.bind('<Button-1>', self._on_click)
        self._draw()
    
    def _lighten_color(self, hex_color):
        hex_color = hex_color.lstrip('#')
        r, g, b = tuple(int(hex_color[i:i+2], 16) for i in (0, 2, 4))
        r = min(255, int(r * 1.15))
        g = min(255, int(g * 1.15))
        b = min(255, int(b * 1.15))
        return f'#{r:02x}{g:02x}{b:02x}'
    
    def _draw(self):
        self.delete('all')
        color = self.hover_color if self.is_hover else self.bg_color
        # Draw rounded rectangle background
        self.create_rectangle(2, 2, self.winfo_reqwidth()-2, self.winfo_reqheight()-2,
                            fill=color, outline='', tags='bg')
        # Draw text centered
        self.create_text(self.winfo_reqwidth()//2, self.winfo_reqheight()//2,
                        text=self.text, fill=self.fg, font=('Segoe UI', 10, 'bold'),
                        tags='text')
    
    def _on_enter(self, e):
        self.is_hover = True
        self._draw()
    
    def _on_leave(self, e):
        self.is_hover = False
        self._draw()
    
    def _on_click(self, e):
        if self.command:
            self.command()


class LexicalAnalyzerApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title('Modern Lexical Analyzer')
        self.geometry('1200x700')
        self.configure(bg='#f0f4f8')
        self.resizable(True, True)
        
        self.symbol_table = {}
        self.token_count = 0
        self.profile_visible = False
        
        self._setup_styles()
        self._create_title_bar()
        self._create_status_bar()
        self._create_main_content()

    def _setup_styles(self):
        style = ttk.Style()
        style.theme_use('clam')
        
        # Treeview styling
        style.configure('Treeview',
                       background='white',
                       foreground='#2c3e50',
                       fieldbackground='white',
                       rowheight=25,
                       font=('Segoe UI', 9))
        style.map('Treeview', background=[('selected', '#4a90e2')])
        style.configure('Treeview.Heading',
                       background='#34495e',
                       foreground='white',
                       font=('Segoe UI', 10, 'bold'))

    def _create_title_bar(self):
        title_frame = tk.Frame(self, bg='#2c3e50', height=60)
        title_frame.pack(fill='x', side='top')
        title_frame.pack_propagate(False)
        
        title = tk.Label(title_frame, text='🔍 Lexical Analyzer Pro',
                        bg='#2c3e50', fg='white',
                        font=('Segoe UI', 18, 'bold'))
        title.pack(side='left', padx=20, pady=15)
        
        subtitle = tk.Label(title_frame, 
                           text='Advanced Token Analysis & Symbol Table Generator',
                           bg='#2c3e50', fg='#95a5a6',
                           font=('Segoe UI', 9))
        subtitle.pack(side='left', padx=(0, 20))

    def _create_main_content(self):
        main_frame = tk.Frame(self, bg='#f0f4f8')
        main_frame.pack(fill='both', expand=True, padx=15, pady=15)
        
        # Left panel - Source Code
        left_panel = tk.Frame(main_frame, bg='white', relief='solid', borderwidth=1)
        left_panel.pack(side='left', fill='both', expand=True, padx=(0, 7))
        
        left_header = tk.Frame(left_panel, bg='#3498db', height=40)
        left_header.pack(fill='x')
        left_header.pack_propagate(False)
        
        tk.Label(left_header, text='📝 Source Code Editor',
                bg='#3498db', fg='white',
                font=('Segoe UI', 12, 'bold')).pack(side='left', padx=15, pady=8)
        
        # Line numbers frame
        line_frame = tk.Frame(left_panel, bg='#ecf0f1', width=40)
        line_frame.pack(side='left', fill='y')
        
        self.line_numbers = tk.Text(line_frame, width=4, padx=5, takefocus=0,
                                    border=0, background='#ecf0f1',
                                    foreground='#7f8c8d', state='disabled',
                                    font=('Consolas', 10))
        self.line_numbers.pack(fill='y', expand=True)
        
        # Source code text
        text_frame = tk.Frame(left_panel)
        text_frame.pack(fill='both', expand=True, padx=5, pady=5)
        
        self.text_source = scrolledtext.ScrolledText(
            text_frame, wrap='none',
            font=('Consolas', 10),
            bg='#fafafa', fg='#2c3e50',
            insertbackground='#e74c3c',
            selectbackground='#3498db',
            selectforeground='white',
            padx=10, pady=10
        )
        self.text_source.pack(fill='both', expand=True)
        self.text_source.bind('<KeyRelease>', self._update_line_numbers)
        self.text_source.bind('<<Modified>>', self._on_text_modified)
        
        # Syntax highlighting tags
        self.text_source.tag_config('keyword', foreground='#9b59b6', font=('Consolas', 10, 'bold'))
        self.text_source.tag_config('datatype', foreground='#3498db', font=('Consolas', 10, 'bold'))
        self.text_source.tag_config('string', foreground='#27ae60')
        self.text_source.tag_config('number', foreground='#e67e22')
        self.text_source.tag_config('comment', foreground='#95a5a6', font=('Consolas', 10, 'italic'))
        
        # Left buttons
        btn_frame_left = tk.Frame(left_panel, bg='white', height=60)
        btn_frame_left.pack(fill='x', pady=10)
        btn_frame_left.pack_propagate(False)
        
        ModernButton(btn_frame_left, '▶ Analyze', self.analyze, 
                    bg='#27ae60', width=120).pack(side='left', padx=(15, 5))
        ModernButton(btn_frame_left, '🗑 Clear', self.clear_source,
                    bg='#e74c3c', width=100).pack(side='left', padx=5)
        ModernButton(btn_frame_left, '📋 Sample', self._load_sample,
                    bg='#95a5a6', width=100).pack(side='left', padx=5)
        ModernButton(btn_frame_left, 'Clear tokenize', self.clear_tokenize,
                    bg='#e67e22', width=130).pack(side='left', padx=5)
        ModernButton(btn_frame_left, 'Symbol Table', self.show_symbol_table,
                    bg='#9b59b6', width=130).pack(side='left', padx=5)
        
        # Right panel - Tokenize
        right_panel = tk.Frame(main_frame, bg='white', relief='solid', borderwidth=1)
        right_panel.pack(side='right', fill='both', expand=True, padx=(7, 0))
        
        right_header = tk.Frame(right_panel, bg='#e74c3c', height=40)
        right_header.pack(fill='x')
        right_header.pack_propagate(False)
        
        tk.Label(right_header, text='🎯 Token Analysis',
                bg='#e74c3c', fg='white',
                font=('Segoe UI', 12, 'bold')).pack(side='left', padx=15, pady=8)
        
        # Token counter
        self.token_label = tk.Label(right_header, text='Tokens: 0',
                                    bg='#e74c3c', fg='white',
                                    font=('Segoe UI', 9))
        self.token_label.pack(side='right', padx=15)
        
        # Treeview
        tree_frame = tk.Frame(right_panel)
        tree_frame.pack(fill='both', expand=True, padx=5, pady=(5, 0))
        
        cols = ('Line', 'Token', 'Type', 'Position')
        self.tree = ttk.Treeview(tree_frame, columns=cols, show='headings', height=18)
        
        self.tree.heading('Line', text='Line #')
        self.tree.heading('Token', text='Token')
        self.tree.heading('Type', text='Token Type')
        self.tree.heading('Position', text='Column')
        
        self.tree.column('Line', width=60, anchor='center')
        self.tree.column('Token', width=180)
        self.tree.column('Type', width=120)
        self.tree.column('Position', width=70, anchor='center')
        
        scrollbar = ttk.Scrollbar(tree_frame, orient='vertical', command=self.tree.yview)
        self.tree.configure(yscrollcommand=scrollbar.set)
        
        self.tree.pack(side='left', fill='both', expand=True)
        scrollbar.pack(side='right', fill='y')
        
        # Load sample code after everything is initialized
        self.after(100, self._load_sample)

    def _create_status_bar(self):
        # Main footer with Visit Developer Profile button
        self.footer_frame = tk.Frame(self, bg='#34495e', height=50)
        self.footer_frame.pack(fill='x', side='bottom')
        self.footer_frame.pack_propagate(False)
        
        # Left side - Status
        self.status_label = tk.Label(self.footer_frame, text='Ready',
                                     bg='#34495e', fg='#ecf0f1',
                                     font=('Segoe UI', 9), anchor='w')
        self.status_label.pack(side='left', padx=15)
        
        # Center - Visit Developer Profile button
        ModernButton(self.footer_frame, '👨‍💻 Visit Developer Profile', 
                    self.toggle_developer_profile,
                    bg='#3498db', width=200, height=32).pack(side='left', padx=20, pady=9)
        
        # Right side - Time
        time_label = tk.Label(self.footer_frame, 
                             text=datetime.now().strftime('%Y-%m-%d %H:%M'),
                             bg='#34495e', fg='#95a5a6',
                             font=('Segoe UI', 9))
        time_label.pack(side='right', padx=15)

    def _update_line_numbers(self, event=None):
        line_count = self.text_source.get('1.0', 'end-1c').count('\n') + 1
        line_numbers_string = '\n'.join(str(i) for i in range(1, line_count + 1))
        
        self.line_numbers.config(state='normal')
        self.line_numbers.delete('1.0', 'end')
        self.line_numbers.insert('1.0', line_numbers_string)
        self.line_numbers.config(state='disabled')

    def _on_text_modified(self, event=None):
        self._update_line_numbers()

    def _load_sample(self):
        sample = """#include<stdio.h>

int main() {
    int num = 42;
    float pi = 3.14159;
    
    // Check if number is positive
    if(num > 0) {
        printf("Positive: %d\\n", num);
    } else {
        printf("Non-positive\\n");
    }
    
    /* Loop demonstration */
    for(int i = 0; i < 5; i++) {
        printf("Iteration: %d\\n", i);
    }
    
    return 0;
}"""
        self.text_source.delete('1.0', 'end')
        self.text_source.insert('1.0', sample)
        self._update_line_numbers()
        self._update_status('Sample code loaded')

    def clear_source(self):
        self.text_source.delete('1.0', 'end')
        self._update_line_numbers()
        self._update_status('Source code cleared')

    def clear_tokenize(self):
        """Clear all tokens from the tree and reset symbol table"""
        for item in self.tree.get_children():
            self.tree.delete(item)
        self.symbol_table.clear()
        self.token_count = 0
        self.token_label.config(text='Tokens: 0')
        self._update_status('Token table cleared')

    def analyze(self):
        source = self.text_source.get('1.0', 'end-1c')
        if not source.strip():
            messagebox.showwarning('Empty Source', 'Please enter source code to analyze.')
            return
        
        self.clear_tokenize()
        lines = source.splitlines()
        self.token_count = 0
        
        for lineno, line in enumerate(lines, start=1):
            tokens = tokenize_line(line)
            col_pos = 0
            for tok, typ in tokens:
                col_pos = line.find(tok, col_pos) + 1
                if typ == 'Identifier':
                    entry = self.symbol_table.get(tok, {'lines': set(), 'count': 0})
                    entry['lines'].add(lineno)
                    entry['count'] += 1
                    self.symbol_table[tok] = entry
                
                self.tree.insert('', 'end', values=(lineno, tok, typ, col_pos))
                self.token_count += 1
                col_pos += len(tok)
        
        self.token_label.config(text=f'Tokens: {self.token_count}')
        self._update_status(f'Analysis complete: {self.token_count} tokens, {len(self.symbol_table)} identifiers')
        messagebox.showinfo('Analysis Complete', 
                           f'Tokenization successful!\n\n'
                           f'Total Tokens: {self.token_count}\n'
                           f'Identifiers: {len(self.symbol_table)}')

    def show_symbol_table(self):
        """Display symbol table in a popup window"""
        if not self.symbol_table:
            messagebox.showinfo('Symbol Table', 'No identifiers found. Run Analyze first.')
            return
        
        win = tk.Toplevel(self)
        win.title('Symbol Table')
        win.geometry('600x450')
        win.configure(bg='#f0f4f8')
        
        header = tk.Frame(win, bg='#9b59b6', height=50)
        header.pack(fill='x')
        header.pack_propagate(False)
        
        tk.Label(header, text='📊 Symbol Table',
                bg='#9b59b6', fg='white',
                font=('Segoe UI', 14, 'bold')).pack(side='left', padx=20, pady=10)
        
        tk.Label(header, text=f'Total Identifiers: {len(self.symbol_table)}',
                bg='#9b59b6', fg='white',
                font=('Segoe UI', 10)).pack(side='right', padx=20)
        
        tree_frame = tk.Frame(win, bg='white')
        tree_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        cols = ('ID', 'Identifier', 'Occurrences', 'Lines')
        tv = ttk.Treeview(tree_frame, columns=cols, show='headings')
        
        tv.heading('ID', text='#')
        tv.heading('Identifier', text='Identifier')
        tv.heading('Occurrences', text='Count')
        tv.heading('Lines', text='Line Numbers')
        
        tv.column('ID', width=50, anchor='center')
        tv.column('Identifier', width=150)
        tv.column('Occurrences', width=100, anchor='center')
        tv.column('Lines', width=250)
        
        scrollbar = ttk.Scrollbar(tree_frame, orient='vertical', command=tv.yview)
        tv.configure(yscrollcommand=scrollbar.set)
        
        tv.pack(side='left', fill='both', expand=True)
        scrollbar.pack(side='right', fill='y')
        
        for idx, (ident, meta) in enumerate(sorted(self.symbol_table.items()), start=1):
            lines = ', '.join(map(str, sorted(meta['lines'])))
            tv.insert('', 'end', values=(idx, ident, meta['count'], lines))

    def toggle_developer_profile(self):
        if self.profile_visible:
            self.profile_frame.destroy()
            self.profile_visible = False
            self.geometry('1200x700')
        else:
            self._show_developer_profile()
            self.profile_visible = True
            # Adjust window height to fit profile
            self.update_idletasks()
            self.geometry('1200x1050')

    def _show_developer_profile(self):
        # Create a popup window for developer profile
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
        tk.Label(header_section, text='Lexical Analyzer Project',
                bg='#e8f4f8', fg='#2c3e50',
                font=('Segoe UI', 18, 'bold')).pack(pady=(5, 2))
        
        # Course info
        tk.Label(header_section, text=' Design for tokenizations 2025',
                bg='#e8f4f8', fg='#7f8c8d',
                font=('Segoe UI', 10)).pack()
        
        # Developer Section
        tk.Label(profile_win, text='Meet the Developers',
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
        
        # Bottom Section - Compiler Construction Project Info
        bottom_section = tk.Frame(profile_win, bg='#5b7fc9', height=80)
        bottom_section.pack(fill='x', pady=(20, 0), side='bottom')
        bottom_section.pack_propagate(False)
        
        tk.Label(bottom_section, text=' Subject: Compiler Constructions Project',
                bg='#5b7fc9', fg='white',
                font=('Segoe UI', 14, 'bold')).pack(pady=(12, 4))
        
        tk.Label(bottom_section, text='Subject Supervisor: Faryal Shamsi',
                bg='#5b7fc9', fg='white',
                font=('Segoe UI', 11)).pack()
        
        # Store reference to prevent garbage collection
        self.profile_window = profile_win

    def _update_status(self, message):
        self.status_label.config(text=message)
        self.after(3000, lambda: self.status_label.config(text='Ready'))


if __name__ == '__main__':
    app = LexicalAnalyzerApp()
    app.mainloop()