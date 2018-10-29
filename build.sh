find ./lectures -iname "*.md" -mindepth 2 -maxdepth 2 -type f -exec sh -c 'pandoc -t revealjs --slide-level=2 -s -o "./docs/$(basename ${0%.md}.html)" "${0}" -V revealjs-url=https://macs-club.github.io/reveal.js -V theme=custom-black' {} \;
