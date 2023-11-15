# Coli-Saar Publications

Web pages for coli-saar publications.


## Creating a page for a new paper

Create a Markdown file at top level; see `slog.md` for an example. This file will be transformed into static HTML using [Jekyll](https://jekyllrb.com/). Your page at `X.md` will be published to `http://coli-saar.github.io/X`.

The file needs to contain the following information in the YAML header:

- `layout: default` - to indicate that the HTML will be generated based on the layout in `_layouts/default.html`.
- `title`: The paper title
- `authors`: The authors of the paper, from left to right. Each author consists of `name`, an `affiliation`, and a `homepage`. Affiliations are specified as numbers here.
- `affiliations`: The authors' affiliations, in order of the numbers. Each affiliation consists of an `id` (the number that was used in the affiliation footnote attached to an author name) and a `name`.

The following entries in the YAML are optional, but highly recommended (where applicable):
- `paper`: The URL to the paper. This can be a PDF hosted within this Github repository, an Arxiv or ACL Anthology link, or anything else.
- `code`: The URL of the code for the paper.
- `data`: The URL to a dataset described in the paper.
- `video`: The URL to a video about the paper.
- `bibtex`: The Bibtex entry for the paper. See the `slog.md` file to see how multi-line content can be specified using YAML's `|` operator.

You can then specify the page content as Markdown. Use h2 (`##`) to separate sections. You can use any Markdown formatting in the content, e.g. to include images. It is a good idea to include lots of images to avoid the feeling of a wall of text. Feel free to add the images to the `static/images` directory; they can then be accessed as `/static/images/image.png` from the Markdown file.


## Offline use

Your paper page will be compiled to HTML every time you push changes to Github. If you want to test it offline before pushing, you can do this:

```
bundle exec jekyll serve
```

You will have to install Ruby and Jekyll before you can do this. Follow the [installation instructions](https://jekyllrb.com/docs/), or if you have a Mac with Apple Silicon, follow these [specialized installation instructions](https://abyte.space/2023/10/install-ruby3-jekyll-macos-apple-silicon).


