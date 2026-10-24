"""One theme implementation for the common site and standalone archives.

Current pages reference shared assets; archived documents embed the same assets
so their local-file and single-file reading workflows continue to work.
"""
import base64
from html import escape
from pathlib import Path
import re

ASSETS = Path(__file__).resolve().parent / "assets"
THEME_CSS = (ASSETS / "theme.css").read_text()
THEME_SCRIPT = (ASSETS / "theme.js").read_text()
FONT_FILES = sorted((ASSETS / "fonts").glob("*"))


def embedded_theme_css():
    """Keep the archived, standalone documents independent of local assets."""
    def embed(match):
        raw = (ASSETS / match[1]).read_bytes()
        return 'url("data:font/woff2;base64,' + base64.b64encode(raw).decode() + '")'
    return re.sub(r'url\("(fonts/[^"\n]+\.woff2)"\)', embed, THEME_CSS)


def theme_head(css_href=None, script_href=None):
    script = (f'<script src="{escape(script_href, quote=True)}"></script>'
              if script_href else f'<script>{THEME_SCRIPT}</script>')
    style = (f'<link rel="stylesheet" href="{escape(css_href, quote=True)}">'
             if css_href else f'<style>{embedded_theme_css()}</style>')
    return '<meta name="color-scheme" content="light dark">' + script + style


def theme_control():
    return ('<label class="theme-control"><span>Theme</span>'
            '<select data-theme-control aria-label="Color theme">'
            '<option value="system">System</option>'
            '<option value="light">Light</option>'
            '<option value="dark">Dark</option></select></label>')
