# Brown CS22 Spring 2024: Lean project


## Directions for setting up GitHub Codespaces

Before following these directions,
you will need to sign up for a [GitHub account](https://github.com/)
if you don't have one already.
This will be useful throughout the rest of your career at Brown CS.
We strongly recommend picking a professional and identifiable username.
For example, Rob is [robertylewis](https://github.com/robertylewis).

We strongly recommend signing up for GitHub's free [student benefits](https://education.github.com/benefits?type=student), 
which include an increased quota on Codespace hours.

Note: we don't expect you to have any experience with git beyond creating a GitHub account!

* If you aren't already there, navigate to the [CS22-Lean-2024 GitHub page](https://github.com/brown-cs22/CS22-Lean-2024).
* Click the green button that says `<> Code`, then select the `Codespaces` tab in the dropdown that appears.
* Click the green button that says `Create Codespace on main`.
* Wait a few minutes for the Codespace to configure itself. Eventually, you'll see a VS Code interface in your browser.
* Once the VS Code interface has loaded, close that tab and return to the [CS22-Lean-2024 GitHub page](https://github.com/brown-cs22/CS22-Lean-2024). Refresh the page.
* Click the green `<> Code` button again, and select the Codespaces tab if it isn't already selected.
* You should now see a Codespace appear in the list under the heading `On current branch`. It will have a random two-word name (e.g., "psychic cod," "cautious memory").
* Click the three dots `⋯` next to that Codespace (*not* the similar icon that appears at the top of the dropdown!).
* Uncheck `Auto-delete Codespace`. The page will reload.
* Open the `<> Code` dropdown to the Codespaces tab once more.
* Click the `⋯` icon next to your Codespace and select `Rename`.
* Give your Codespace a recognizable name. We suggest `CS22 Lean`.

You're all set up!

In the future, you should bookmark your Codespace URL (which should be of the form `word-word-randomLettersAndNumbers.github.dev`) and access it that way, or use the Codespaces dropdown on the GitHub page.

If at any point your workspace becomes unusable
and you think you need a fresh start, you can create a new Codespace from the dropdown on the GitHub page.

## Directions for updating 

We will push more lecture demos and homework assignments to this project throughout the semester.
To pull them into your Codespace, follow these directions:

* Open the terminal in your Codespace if it is not already open. 
* Run the command `pull-updates`.

We will try not to let this happen, but occasionally, we might change files that you have edited yourself.
The `pull-updates` script should notice this and not overwrite your changes.
But if there are conflicts, you may have to reset your work.
(Feel free to copy your changes to another file if you want.)
Running the command `reset-all` and then `pull-updates` again should clean things up.

## git: the fine print 

This is a GitHub repository, 
and your workspace will interact with our course materials using git.
We do *not* expect you to have any experience or knowledge of git
beyond having a GitHub account.
If you do know how to use git and would like to use proper version control in your workspace,
you are welcome to, but our course staff is not responsible for helping!
We document the setup here for your reference.

* We will try our best not to modify files in the `BrownCs22/Demos` directory after we add them.
  This should minimize merge conflicts if you edit files there.
* Official course materials,
  including lecture demos and homeworks,
  will be pushed to the `main` branch of this repository.
  You will have to pull these changes to your workspace.
* The `pull-updates` script in your workspace
  will `git stash` any uncommitted changes you have,
  pull our updates,
  and `git stash pop` your changes back.
  If your changes conflict with ours, 
  it will leave your project unmodified and print an error message.
  This script assumes you have not made any commits of your own;
  if you have, you're on your own!
* The `reset-all` script resets all tracked files to the most recent commit.
