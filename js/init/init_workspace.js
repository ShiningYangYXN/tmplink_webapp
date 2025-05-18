function INIT_workspace() {
    TL.ready(() => {
        //判断是否登录
        if (TL.isLogin() === false) {
            //跳转到登录页面
            app.open('/app&listview=login');
            return;
        }
        // 直接调用filelist(0)，AutoLoader会自动处理启用和加载
        TL.workspace_filelist(0);
        TL.workspace_navbar();
        app.languageBuild();
        $('title').html(app.languageData.title_workspace);
        $('meta[name=description]').html(app.languageData.des_workspace);
    });
}