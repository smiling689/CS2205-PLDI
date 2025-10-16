# README 
This is the repo for the class CS 2205, Programming Language - Design and Implementation.

The website this year is [web](https://jhc.sjtu.edu.cn/public/courses/CS2205/)

**环境配置**

一般方法：在课程网站上下载并安装Coq-Platform\~8.20\~2025.01，在vscode中安装VsCoq插件，并手动把版本调整为2.2.3或更低的版本后关闭自动更新，在插件的设置的 Vscoq Path中填入Coq-Platform\~8.20~2025\bin，就可以使用快捷键alt+→和alt+↓来运行文件。

如果你安装过Vscoq Legacy，则需要卸载该插件。

windows需要自行提供CONFIGURE文件用于提供相关依赖的地址，请在CS2205-2025fall目录下新建一个无后缀名文件CONFIGURE，然后将coq安装的路径写入该文件中。

如果你已经把coq的bin加入了环境变量，或者是在wsl下使用opam安装的coq，那么不需要CONFIGURE也可以完成相关的设置。

以cygwin编译环境下的CONFIGURE设置为例：
```
COQBIN=/cygdrive/d/Coq-8.20.1/bin/
SUF=   // 这里写SUF=.exe也可以
```
如果你的编译环境是windows的powershell, CONFIGURE设置为
```
COQBIN=D:\Coq-8.20.1\bin\\
SUF=.exe
```
如果你的编译环境是wsl，CONFIGURE设置为
```
COQBIN=/mnt/d/Coq-8.20.1/bin/
SUF=.exe
```

**文件编译**

我们在本仓库中内置了makefile文件，在vscode的终端中直接运行make即可完成编译。如果你需要增加或修改编译的文件，可以自行修改makefile的内容。

编译之前请先确认你的环境中是否有make，具体指令为:
```
make --version
```
如果没有，可以使用mingw32-make或者mingw64-make替代，当然也要确认环境中存在
```
mingw32-make --version
```
或是
```
mingw64-make --version
```

首先如果子模块（比如sets）有更新，需要先
```
git submodule init
git submodule update
```

正式编译之前请先计算依赖，具体指令为：（这里如果你使用其它make，请做对应替换）
```
make depend
```
然后可以开始编译，具体指令为：
```
make
```
如果你希望他并发加速，那么可以使用make -j4，其中数字可以自由调整，具体取决于你的电脑有多少个核

**补充说明**

通常我们会在文件资源管理中隐藏coq的编译文件，如.vo文件。你可以在vscode的设置的files.excluded中加入规则
```
**/*.vo
```
来实现。

如果你需要修改vscoq的执行快捷键，你可以：先
```
Ctrl + Shift + P
```
打开vscode的控制面板，输入
```
Pereferences:Open Keyboard Shortcuts
```
后搜索你当前使用的快捷键，然后改变其绑定的按键组合。