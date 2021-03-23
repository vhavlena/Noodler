"""
Auxiliary functions for Noodler
"""

from IPython.display import display, HTML, SVG


def display_inline(*args, per_row=None, show=None, vert_align="text-top"):
    """
    This is a wrapper around IPython's `display()` to display multiple
    elements in a row, without forced line break between them.

    If the `per_row` argument is given, at most `per_row` arguments are
    displayed on each row, each one taking 1/per_row of the line width.
    """
    width = res = ''
    if per_row:
        width = f'width:{100//per_row}%;'
    for arg in args:
        dpy = 'inline-block'
        if show is not None and hasattr(arg, 'show'):
            rep = arg.show(show)._repr_svg_()
        elif hasattr(arg, '_repr_svg_'):
            rep = arg._repr_svg_()
        elif hasattr(arg, '_repr_html_'):
            rep = arg._repr_html_()
        elif hasattr(arg, '_repr_latex_'):
            rep = arg._repr_latex_()
            if not per_row:
                dpy = 'inline'
        else:
            rep = str(arg)
        res += (f"<div style='vertical-align:{vert_align};" +
                f"display:{dpy};{width}'>{rep}</div>")
    display(HTML(res))


def show_automata(automata):
    """
    Show constraint automata for variables.

    Parameters
    ----------
    automata : list of auts or dict (str → aut)
        Automata to display. If dict is given, keys are interpreted
        as names.

    Returns
    -------
    None
    """
    if isinstance(automata, dict):
        for name, aut in automata.items():
            display_inline(f"{name}:", SVG(aut.svg()),
                           vert_align="middle")
    else:
        for aut in automata:
            aut.display()
