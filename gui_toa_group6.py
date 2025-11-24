# gui_toa_group6_full.py
import os
import webbrowser
import tkinter as tk
from tkinter import messagebox, scrolledtext

from collections import defaultdict, deque
from itertools import combinations
import graphviz

EPS = 'ε'

# ------------------------
#   NFA Structures
# ------------------------
class NFA:
    def __init__(self):
        self.states = set()
        self.start = None
        self.accept = None
        self.trans = defaultdict(lambda: defaultdict(set))

    def add_state(self, q):
        self.states.add(q)

    def add_transition(self, a, symbol, b):
        self.add_state(a)
        self.add_state(b)
        self.trans[a][symbol].add(b)

# -------------------------
#   State counter
# -------------------------
_state_counter = 0
def new_state():
    global _state_counter
    _state_counter += 1
    return f"q{_state_counter}"

# -------------------------
#   Basic NFA constructors
# -------------------------
def nfa_for_symbol(sym):
    n = NFA()
    s = new_state(); t = new_state()
    n.start = s; n.accept = t
    n.add_transition(s, sym, t)
    return n

def nfa_concat(n1, n2):
    n = NFA()
    for st in n1.states | n2.states:
        n.add_state(st)
    n.start = n1.start
    n.accept = n2.accept
    for a, d in n1.trans.items():
        for sym, dests in d.items():
            for b in dests:
                n.add_transition(a, sym, b)
    for a, d in n2.trans.items():
        for sym, dests in d.items():
            for b in dests:
                n.add_transition(a, sym, b)
    n.add_transition(n1.accept, EPS, n2.start)
    return n

def nfa_union(n1, n2):
    n = NFA()
    s = new_state(); t = new_state()
    n.start = s; n.accept = t
    for st in n1.states | n2.states:
        n.add_state(st)
    for a, d in n1.trans.items():
        for sym, dests in d.items():
            for b in dests:
                n.add_transition(a, sym, b)
    for a, d in n2.trans.items():
        for sym, dests in d.items():
            for b in dests:
                n.add_transition(a, sym, b)
    n.add_transition(s, EPS, n1.start)
    n.add_transition(s, EPS, n2.start)
    n.add_transition(n1.accept, EPS, t)
    n.add_transition(n2.accept, EPS, t)
    return n

def nfa_star(n1):
    n = NFA()
    s = new_state(); t = new_state()
    n.start = s; n.accept = t
    for st in n1.states:
        n.add_state(st)
    for a, d in n1.trans.items():
        for sym, dests in d.items():
            for b in dests:
                n.add_transition(a, sym, b)
    n.add_transition(s, EPS, n1.start)
    n.add_transition(s, EPS, t)
    n.add_transition(n1.accept, EPS, n1.start)
    n.add_transition(n1.accept, EPS, t)
    return n

# -------------------------
#   Build Group-6 Regex NFA
# -------------------------
def build_group6_nfa():
    global _state_counter
    _state_counter = 0

    # ed
    Ned = nfa_concat(nfa_for_symbol('e'), nfa_for_symbol('d'))
    # ee
    Nee = nfa_concat(nfa_for_symbol('e'), nfa_for_symbol('e'))

    # f(d|dd|ddd)*
    d1 = nfa_for_symbol('d')
    dd = nfa_concat(nfa_for_symbol('d'), nfa_for_symbol('d'))
    ddd = nfa_concat(dd, nfa_for_symbol('d'))
    union_inner = nfa_union(d1, nfa_union(dd, ddd))
    star_inner = nfa_star(union_inner)
    f_part = nfa_concat(nfa_for_symbol('f'), star_inner)

    # Combine all three parts
    combined = nfa_union(nfa_union(Ned, Nee), f_part)

    # Create a single unified accept state
    accept_state = new_state()
    for part in [Ned, Nee, f_part]:
        combined.add_transition(part.accept, EPS, accept_state)
    combined.accept = accept_state
    combined.add_state(accept_state)

    return combined


# -------------------------
#   NFA -> DFA
# -------------------------
def epsilon_closure(nfa, states):
    s = list(states)
    closure = set(states)
    while s:
        st = s.pop()
        for t in nfa.trans[st].get(EPS, []):
            if t not in closure:
                closure.add(t)
                s.append(t)
    return closure

def move(nfa, states, symbol):
    res = set()
    for st in states:
        for t in nfa.trans[st].get(symbol, []):
            res.add(t)
    return res

class DFA:
    def __init__(self):
        self.states = set()
        self.start = None
        self.accepts = set()
        self.trans = dict()
        self.symbols = set()

# -------------------------
#   Transition Table Helpers
# -------------------------
def nfa_table_str(nfa):
    output = "\nNFA Transition Table\n"
    output += f"(ε shown as '{EPS}')\n\n"
    states = sorted(nfa.states)
    symbols = sorted({s for tr in nfa.trans.values() for s in tr.keys()})
    header = ["State"] + symbols
    output += "{:<8}".format(header[0]) + "".join(f"{sym:^12}" for sym in header[1:]) + "\n"
    output += "-" * (8 + 12 * len(symbols)) + "\n"
    for s in states:
        row = "{:<8}".format(s)
        for sym in symbols:
            dests = sorted(nfa.trans[s].get(sym, []))
            row += "{:^12}".format(",".join(dests) if dests else "-")
        output += row + "\n"
    return output

def dfa_table_str(dfa):
    output = "\nDFA Transition Table\n\n"
    syms = sorted(dfa.symbols)
    header = ["State"] + syms
    output += "{:<20}".format(header[0]) + "".join(f"{sym:^18}" for sym in header[1:]) + "\n"
    output += "-" * (20 + 18 * len(syms)) + "\n"
    for st in sorted(dfa.states, key=lambda s: sorted(s)):
        label = "{" + ",".join(sorted(st)) + "}"
        row = "{:<20}".format(label)
        for a in syms:
            nxt = dfa.trans.get(st, {}).get(a)
            if nxt:
                row += "{:^18}".format("{" + ",".join(sorted(nxt)) + "}")
            else:
                row += "{:^18}".format("-")
        output += row + "\n"
    return output

def min_dfa_table_str(dfa):
    output = "\nMinimized DFA Transition Table\n\n"
    syms = sorted(dfa.symbols)
    header = ["State"] + syms
    output += "{:<20}".format(header[0]) + "".join(f"{sym:^18}" for sym in header[1:]) + "\n"
    output += "-" * (20 + 18 * len(syms)) + "\n"
    for st in sorted(dfa.states, key=lambda s: sorted(s)):
        label = "{" + ",".join(sorted(st)) + "}"
        row = "{:<20}".format(label)
        for a in syms:
            nxt = dfa.trans.get(st, {}).get(a)
            if nxt:
                row += "{:^18}".format("{" + ",".join(sorted(nxt)) + "}")
            else:
                row += "{:^18}".format("-")
        output += row + "\n"
    return output

# -------------------------
#   NFA -> DFA Conversion
# -------------------------
def nfa_to_dfa(nfa):
    dfa = DFA()
    syms = set()
    for s, d in nfa.trans.items():
        for sym in d:
            if sym != EPS:
                syms.add(sym)
    dfa.symbols = syms
    start = frozenset(epsilon_closure(nfa, {nfa.start}))
    dfa.start = start
    dfa.states.add(start)
    queue = deque([start])
    dfa.trans[start] = {}
    while queue:
        T = queue.popleft()
        dfa.trans[T] = {}
        for a in syms:
            U = epsilon_closure(nfa, move(nfa, T, a))
            Uf = frozenset(U)
            if not Uf:
                continue
            if Uf not in dfa.states:
                dfa.states.add(Uf)
                queue.append(Uf)
            dfa.trans[T][a] = Uf
    for s in dfa.states:
        if nfa.accept in s:
            dfa.accepts.add(s)
    return dfa

# -------------------------
#   DFA Minimization
# -------------------------
def minimize_dfa(dfa):
    states = list(dfa.states)
    n = len(states)
    index = {s: i for i, s in enumerate(states)}
    table = [[False] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if (states[i] in dfa.accepts) != (states[j] in dfa.accepts):
                table[i][j] = True
    changed = True
    while changed:
        changed = False
        for i in range(n):
            for j in range(i + 1, n):
                if table[i][j]:
                    continue
                for a in dfa.symbols:
                    t1 = dfa.trans.get(states[i], {}).get(a)
                    t2 = dfa.trans.get(states[j], {}).get(a)
                    if t1 is None or t2 is None:
                        continue
                    ii = index[t1]
                    jj = index[t2]
                    x, y = min(ii, jj), max(ii, jj)
                    if table[x][y]:
                        table[i][j] = True
                        changed = True
                        break
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra
    for i in range(n):
        for j in range(i + 1, n):
            if not table[i][j]:
                union(i, j)
    classes = {}
    for i in range(n):
        r = find(i)
        if r not in classes:
            classes[r] = []
        classes[r].append(states[i])
    min_dfa = DFA()
    rep_map = {}
    for rep, members in classes.items():
        new_state_frozen = frozenset({st for m in members for st in m})
        min_dfa.states.add(new_state_frozen)
        rep_map[rep] = new_state_frozen
    orig_to_class = {}
    for rep, members in classes.items():
        for m in members:
            orig_to_class[m] = rep_map[rep]
    min_dfa.start = orig_to_class[dfa.start]
    for s in dfa.accepts:
        min_dfa.accepts.add(orig_to_class[s])
    min_dfa.symbols = dfa.symbols
    min_dfa.trans = {}
    for st in min_dfa.states:
        min_dfa.trans[st] = {}
    for s in dfa.states:
        cls = orig_to_class[s]
        for a, dest in dfa.trans.get(s, {}).items():
            min_dfa.trans[cls][a] = orig_to_class[dest]
    return min_dfa

# -------------------------
#   Formatting & Drawing
# -------------------------
def format_state(st):
    if isinstance(st, frozenset):
        return "{" + ",".join(sorted(st)) + "}"
    return str(st)

def draw_graph(dfa_or_nfa, filename, is_dfa=True):
    dot = graphviz.Digraph(
        comment="Automaton Diagram",
        format="png",
        graph_attr={"rankdir": "LR", "fontsize": "20", "bgcolor": "white", "ranksep": "1", "nodesep": "0.7"},
        node_attr={"shape": "circle", "style": "filled", "fontsize": "16", "penwidth": "2", "fontname": "Helvetica"},
        edge_attr={"fontsize": "14", "fontname": "Helvetica", "arrowsize": "0.8"}
    )

    start_node = "__start"
    dot.node(start_node, "", shape="point", color="#009900", width="0.4")

    states = getattr(dfa_or_nfa, "states")
    accepts = getattr(dfa_or_nfa, "accepts", {getattr(dfa_or_nfa, 'accept', None)})
    start = getattr(dfa_or_nfa, "start")

    for s in states:
        label = "{" + ",".join(sorted(s)) + "}" if isinstance(s, frozenset) else s
        color = "#b3e0ff" if s in accepts else "#c6efce" if s == start else "#f7f7f7"
        shape = "doublecircle" if s in accepts else "circle"
        dot.node(label, label, fillcolor=color, shape=shape)

    # Start edge
    start_label = "{" + ",".join(sorted(start)) + "}" if isinstance(start, frozenset) else start
    dot.edge(start_node, start_label, color="#009900", penwidth="2")

    # Add transitions
    trans = getattr(dfa_or_nfa, "trans")
    for src, dests in trans.items():
        src_label = "{" + ",".join(sorted(src)) + "}" if isinstance(src, frozenset) else src
        for sym, tgt_set in dests.items():
            if not is_dfa:
                for tgt in tgt_set:
                    dot.edge(src_label, tgt, label=sym)
            else:
                tgt_label = "{" + ",".join(sorted(tgt_set)) + "}" if isinstance(tgt_set, frozenset) else tgt_set
                dot.edge(src_label, tgt_label, label=sym)
    dot.render(filename, cleanup=True)

# -------------------------
#   Simulation
# -------------------------
def simulate(dfa, string):
    log = []
    state = dfa.start
    log.append(f"Start at {format_state(state)}")
    step_num = 1
    for ch in string:
        nxt = dfa.trans.get(state, {}).get(ch)
        step_text = f"[Step {step_num}] {format_state(state)} --{ch}--> "
        if nxt is None:
            step_text += "NO TRANSITION"
            log.append(step_text)
            return log, False
        step_text += f"{format_state(nxt)}"
        log.append(step_text)
        state = nxt
        step_num += 1
    if state in dfa.accepts:
        log.append(f" FINAL STATE REACHED: {format_state(state)}")
        return log, True
    else:
        log.append(f"✘ STOPPED AT NON-FINAL STATE: {format_state(state)}")
        return log, False

# -------------------------
#   GLOBALS
# -------------------------
GLOBAL_NFA = None
GLOBAL_DFA = None
GLOBAL_MIN_DFA = None

# -------------------------
#   GUI FUNCTIONS
# -------------------------
def gui_build_nfa():
    global GLOBAL_NFA
    GLOBAL_NFA = build_group6_nfa()
    output_box.delete(1.0, tk.END)
    output_box.insert(tk.END, "✔ NFA Built Successfully!\n")
    output_box.insert(tk.END, nfa_table_str(GLOBAL_NFA))
    draw_graph(GLOBAL_NFA, "nfa", False)
    output_box.insert(tk.END, "\nNFA diagram saved as nfa.png\n")

def gui_build_dfa():
    global GLOBAL_NFA, GLOBAL_DFA
    if GLOBAL_NFA is None:
        messagebox.showerror("Error", "Build NFA first!")
        return
    GLOBAL_DFA = nfa_to_dfa(GLOBAL_NFA)
    output_box.delete(1.0, tk.END)
    output_box.insert(tk.END, "✔ DFA Built Successfully!\n")
    output_box.insert(tk.END, dfa_table_str(GLOBAL_DFA))
    draw_graph(GLOBAL_DFA, "dfa", True)
    output_box.insert(tk.END, "\nDFA diagram saved as dfa.png\n")

def gui_minimize_dfa():
    global GLOBAL_DFA, GLOBAL_MIN_DFA
    if GLOBAL_DFA is None:
        messagebox.showerror("Error", "Build DFA first!")
        return
    GLOBAL_MIN_DFA = minimize_dfa(GLOBAL_DFA)
    output_box.delete(1.0, tk.END)
    output_box.insert(tk.END, "✔ DFA Minimized Successfully!\n")
    output_box.insert(tk.END, min_dfa_table_str(GLOBAL_MIN_DFA))
    draw_graph(GLOBAL_MIN_DFA, "dfa_minimized", True)
    output_box.insert(tk.END, "\nMinimized DFA diagram saved as dfa_minimized.png\n")

def gui_simulate():
    global GLOBAL_MIN_DFA
    if GLOBAL_MIN_DFA is None:
        messagebox.showerror("Error", "Minimize DFA first!")
        return
    s = input_entry.get()
    log, accepted = simulate(GLOBAL_MIN_DFA, s)
    output_box.delete(1.0, tk.END)
    output_box.insert(tk.END, f"Simulating string: '{s}'\n\n")
    for line in log:
        output_box.insert(tk.END, line + "\n")
    if accepted:
        output_box.insert(tk.END, "\n✔ STRING ACCEPTED\n", "green")
    else:
        output_box.insert(tk.END, "\n✘ STRING REJECTED\n", "red")

def open_diagram(filename):
    if not filename.lower().endswith('.png'):
        filename += ".png"
    if os.path.exists(filename):
        webbrowser.open(filename)
    else:
        messagebox.showerror("Error", f"{filename} not found! Build it first.")

def gui_clear_output():
    output_box.delete(1.0, tk.END)

# -------------------------
#   BUILD GUI
# -------------------------
root = tk.Tk()
root.title("TOA Project - Group 6 Regex Engine")

frame1 = tk.Frame(root)
frame1.pack(pady=5)
tk.Button(frame1, text="Build NFA", command=gui_build_nfa).pack(side=tk.LEFT, padx=5)
tk.Button(frame1, text="Build DFA", command=gui_build_dfa).pack(side=tk.LEFT, padx=5)
tk.Button(frame1, text="Minimize DFA", command=gui_minimize_dfa).pack(side=tk.LEFT, padx=5)
tk.Button(frame1, text="Clear Output", command=gui_clear_output).pack(side=tk.LEFT, padx=5)

frame2 = tk.Frame(root)
frame2.pack(pady=5)
tk.Label(frame2, text="Input String:").pack(side=tk.LEFT)
input_entry = tk.Entry(frame2)
input_entry.pack(side=tk.LEFT, padx=5)
tk.Button(frame2, text="Simulate", command=gui_simulate).pack(side=tk.LEFT, padx=5)

frame3 = tk.Frame(root)
frame3.pack(pady=5)
tk.Button(frame3, text="Open NFA Diagram", command=lambda: open_diagram("nfa.png")).pack(side=tk.LEFT, padx=5)
tk.Button(frame3, text="Open DFA Diagram", command=lambda: open_diagram("dfa.png")).pack(side=tk.LEFT, padx=5)
tk.Button(frame3, text="Open Minimized DFA Diagram", command=lambda: open_diagram("dfa_minimized.png")).pack(side=tk.LEFT, padx=5)

output_box = scrolledtext.ScrolledText(root, width=120, height=30, font=("Consolas", 11))
output_box.pack(padx=10, pady=10)

output_box.tag_config("green", foreground="green")
output_box.tag_config("red", foreground="red")

root.mainloop()

