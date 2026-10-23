"""One theme implementation for the common site and standalone archives.

Current pages reference shared assets; archived documents embed the same assets
so their local-file and single-file reading workflows continue to work.
"""
from html import escape
from pathlib import Path

ASSETS = Path(__file__).resolve().parent / "assets"
THEME_CSS = (ASSETS / "theme.css").read_text()
THEME_SCRIPT = (ASSETS / "theme.js").read_text()


def theme_head(css_href=None, script_href=None):
    script = (f'<script src="{escape(script_href, quote=True)}"></script>'
              if script_href else f'<script>{THEME_SCRIPT}</script>')
    style = (f'<link rel="stylesheet" href="{escape(css_href, quote=True)}">'
             if css_href else f'<style>{THEME_CSS}</style>')
    return '<meta name="color-scheme" content="light dark">' + script + style


def theme_control():
    return ('<label class="theme-control"><span>Theme</span>'
            '<select data-theme-control aria-label="Color theme">'
            '<option value="system">System</option>'
            '<option value="light">Light</option>'
            '<option value="dark">Dark</option></select></label>')
