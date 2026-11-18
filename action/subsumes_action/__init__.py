"""The code of the subsumes GitHub Action.

It compares the schemas of a checkout with the same files in an earlier commit and reports
what each change does: whether the schema still accepts everything it did, and whether it
accepts anything new. ``action.yml`` at the root of the repository runs it, and it is no
tool to be run by hand.
"""
