Download Hugo:
```pwsh
winget install Hugo.Hugo.Extended
```

Create the site and set up a theme:
```sh
hugo new site hugo-source --format yaml
cd hugo-source
#git clone https://github.com/adityatelange/hugo-PaperMod themes/PaperMod --depth=1
git submodule add --depth=1 https://github.com/adityatelange/hugo-PaperMod.git themes/PaperMod
git submodule update --init --recursive
cd themes/PaperMod
git pull
cd ../..
# sed '1s/ .*/ /' hugo.yaml
sed -i '1s/ .*/ #https:\/\/danzuep.github.io\/SchedulePlanner/' hugo.yaml
sed -i '2s/en-us/en-gb/' hugo.yaml
sed -i '3s/ .*/ Schedule Planner/' hugo.yaml
cat <<EOF >> hugo.yaml
params.description: Schedule Planner demo
params.author: Daniel Collingwood
theme: ["PaperMod"]
EOF
cat <<EOF >> hugo.yaml
theme: ["PaperMod"]
params:
  description: Schedule Planner demo
  author: Daniel Collingwood
EOF
hugo new content/_index.md
# hugo new content/posts/demo/index.md
# hugo server
```

Go to the Settings tab of your repository and enable GitHub Pages from GitHub Actions (workflows).