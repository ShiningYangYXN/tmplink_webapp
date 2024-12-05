class dir {
    parent_op = null
    room = {}
    subroom_data = {}
    file_list = []

    init(parent_op) {
        this.parent_op = parent_op;
    }


    viewByList(data, page) {
        let url_params = get_url_params();
        this.btnActiveReset();
        $('#room_btn_file_list').addClass('text-blue');
        if (page == 0 || page == 'all') {
            $('#dir_list').html('');
            if (this.subroom_data.length != 0) {
                $('#dir_list').append(app.tpl('dir_list_tpl', this.subroom_data));
            }
            if (data === false && this.subroom_data == 0 && url_params.mrid != 0) {
                $('.no_files').show();
            }
            if (data === false && this.subroom_data == 0 && url_params.mrid == '0') {
                $('.no_dir').show();
            }
        }
        if (data.length != 0) {
            $('#dir_list').append(app.tpl('dir_filelist_tpl', data));
        }
        $('.lefttime-remainder').each((i, e) => {
            let id = $(e).attr('id');
            let time = $(e).attr('data-tmplink-lefttime');
            this.parent_op.countTimeDown(id, time);
        });
        this.parent_op.btn_copy_bind();
        app.linkRebind();
    }

    viewByPhoto(data, page) {
        this.btnActiveReset();
        $('#room_btn_file_photo').addClass('text-blue');
        if (page == 0 || page == 'all') {
            $('#dir_list').html('');
            if (this.subroom_data.length != 0) {
                $('#dir_list').append(app.tpl('dir_list_tpl', this.subroom_data));
            }
            if (data === false && this.subroom_data == 0) {
                $('.no_photos').show();
            }
        }
        if (data.length != 0) {
            $('#dir_list').append(app.tpl('dir_photolist_tpl', data));
        }
        this.parent_op.btn_copy_bind();
        app.linkRebind();
        this.parent_op.lazyload('.lazyload');
    }

    deleteFile(ukey) {
        var params = get_url_params();
        if (this.parent_op.profile_confirm_delete_get()) {
            if (!confirm(app.languageData.confirm_delete)) {
                return false;
            }
        }
        $('.file_unit_' + ukey).hide();
        $.post(this.parent_op.api_mr, {
            action: 'file_del',
            token: this.parent_op.api_token,
            //captcha: recaptcha,
            mr_id: params.mrid,
            ukey: ukey
        }, () => {
            //this.dir.filelist();
        });
    }

    create() {
        var name = $('#modal_meetingroom_create_name').val();
        var model = $('#modal_meetingroom_create_type').val();
        var mr_id = $('#mr_id').val();
        var parent = $('#mr_parent_id').val();
        var top = $('#mr_top_id').val();
        if (model == '' && name == '') {
            $('#notice_meetingroom_create').html(app.languageData.notice_meetingroom_status_mrcreat_fail);
            return false;
        }
        if (parent > 0) {
            model = 0;
        }
        $('#modal_meetingroom_create_btn').attr('disabled', true);
        $('#notice_meetingroom_create').html(app.languageData.notice_meetingroom_status_proccessing);
        this.parent_op.recaptcha_do('mr_add', (recaptcha) => {
            $.post(this.parent_op.api_mr, {
                action: 'create',
                token: this.parent_op.api_token,
                //captcha: recaptcha,
                name: name,
                mr_id: mr_id,
                parent: parent,
                top: top,
                model: model
            }, (rsp) => {
                if (rsp.status == 1) {
                    $('#notice_meetingroom_create').html(app.languageData.notice_meetingroom_status_mrcreated);
                    this.open();
                    $('#mrCreaterModal').modal('hide');
                    //更新文件夹树形图
                    this.treeGet();
                } else {
                    $('#notice_meetingroom_create').html(app.languageData.notice_meetingroom_status_mrcreat_fail);
                }
                setTimeout(() => {
                    $('#modal_meetingroom_create_btn').removeAttr('disabled');
                }, 2000);
            });
        });
    }

    delete(mrid, group_delete = false) {
        if (this.parent_op.profile_confirm_delete_get() && group_delete === false) {
            if (!confirm(app.languageData.confirm_delete)) {
                return false;
            }
        }

        //if mrid is array, then delete all
        if (group_delete) {
            for (let i in mrid) {
                $('#meetingroom_id_' + mrid[i]).fadeOut();
            }
        } else {
            $('#meetingroom_id_' + mrid).fadeOut();
        }

        $.post(this.parent_op.api_mr, {
            action: 'delete',
            token: this.parent_op.api_token,
            mr_id: mrid
        }, () => {
            this.open();
        });
    }

    reName(mrid) {
        var newname = prompt(app.languageData.modal_meetingroom_newname, "");
        if (newname === null) {
            return false;
        }
        $.post(this.parent_op.api_mr, {
            action: 'rename',
            token: this.parent_op.api_token,
            name: newname,
            mr_id: mrid
        }, (rsp) => {
            this.open();
        });
    }

    setModel(type) {
        let room_key = 'app_room_view_' + this.room.mr_id;
        switch (type) {
            case 'photo':
                localStorage.setItem(room_key, 'photo');
                break;
            case 'list':
                localStorage.setItem(room_key, 'list');
                break;
            default:
                localStorage.setItem(room_key, 'list');
        }
        this.filelist(0);
    }

    listModel(data, page, room_id) {
        let room_key = 'app_room_view_' + room_id;
        switch (localStorage.getItem(room_key)) {
            case 'photo':
                this.viewByPhoto(data, page);
                break;
            case 'list':
                this.viewByList(data, page);
                break;
            default:
                this.viewByList(data, page);
        }
        this.parent_op.is_file_ok_check(data);
    }

    report() {
        var mr_id = this.room.mr_id;
        var reason = $('#room_report_model').val();
        $('#room_reportbtn').attr('disabled', true);
        $('#room_reportbtn').html(`<span class="text-red">${app.languageData.form_btn_processed}</span>`);
        $.post(this.api_mr, {
            'action': 'report',
            'token': this.api_token,
            'reason': reason,
            'mr_id': mr_id
        }, (rsp) => {
            $('#room_reportbtn').html(app.languageData.form_btn_processed);
        }, 'json');
    }

    total(mrid) {
        $('.room_subinfo').hide();
        $('#room_total').html('');
        if (mrid == 0) {
            return false;
        }
        $.post(this.parent_op.api_mr, {
            action: 'total', mr_id: mrid, token: this.parent_op.api_token
        }, (rsp) => {
            if (rsp.data.nums > 0) {
                $('.room_subinfo').show();
                let total_size_text = bytetoconver(rsp.data.size, true);
                $('#room_total').html(`${rsp.data.nums} ${app.languageData.total_units_of_file} , ${total_size_text}`);
                this.mobileTopabrFix(mr_id);
            }
        }, 'json');
    }

    open() {
        var params = get_url_params();
        $('#room_userlist').hide();
        $('.permission-room-file').hide();
        $('.permission-room-user').hide();
        $('.data_loading').show();
        //清理数据
        $('#dir_list').html('');
        $('#room_direct_model').hide();
        $('.room_subinfo').hide();
        //this.loadingON();
        //获取基本信息
        $.post(this.parent_op.api_mr, {
            action: 'details',
            //captcha: recaptcha,
            token: this.parent_op.api_token,
            mr_id: params.mrid
        }, (rsp) => {
            this.room_data = rsp.data;
            $('.data_loading').hide();
            this.loadingOFF();
            if (rsp.status === 0) {
                //会议室不存在了
                this.room.parent = 0;
                this.room.top = 0;
                this.room.ownner = 0;
                this.room.mr_id = 0;
                app.open('/404');
                this.parent_op.ga('Dir-Unavailable');
                return false;
            }
            //会议室不可用
            if (rsp.data.status == 'reported' && rsp.data.owner == 0) {
                this.room.parent = 0;
                this.room.top = 0;
                this.room.ownner = 0;
                this.room.mr_id = 0;
                app.open('/404');
                this.parent_op.ga('Dir-Reported');
                return false;
            }

            //room need to login
            if (rsp.status === 3) {
                //设定登录后跳转的页面
                localStorage.setItem('return_page', getCurrentURL());
                app.open('/app&listview=login');
                return false;
            }
            this.parent_op.ga('Dir-' + rsp.data.name);
            //更新统计信息
            this.total(rsp.data.mr_id);
            this.room.parent = rsp.data.parent;
            this.room.top = rsp.data.top;
            this.room.owner = rsp.data.owner;
            this.room.mr_id = rsp.data.mr_id;
            this.room.display = rsp.data.display;
            this.room.sort_by = rsp.data.sort_by;
            this.room.sort_type = rsp.data.sort_type;
            this.room.status = rsp.data.status;
            this.room.allow_upload = rsp.data.allow_upload;
            this.room.img_link = rsp.data.img_link;
            this.room.model = rsp.data.model;
            this.room.ui_avatar_id = rsp.data.ui_avatar_id;
            this.room.ui_publish = rsp.data.ui_publish;
            this.room.ui_publish_status = rsp.data.ui_publish_status;
            this.room.ui_nickname = rsp.data.ui_nickname;
            this.room.ui_intro = rsp.data.ui_intro;
            this.room.ui_pro = rsp.data.ui_pro;
            this.room.publish = rsp.data.publish;

            this.performanceInit(this.room.display, this.room.sort_by, this.room.sort_type);

            //如果 room id 是0，则显示特定的顶部
            if (params.mrid == 0) {
                $('#title_of_root').show();
                $('#title_of_sub').hide();
            } else {
                $('#title_of_root').hide();
                $('#title_of_sub').show();
            }

            //如果用户是拥有者，显示直链相关的信息，并初始化
            if (this.room.owner == 1) {
                this.parent_op.direct.dirRoomInit();
                $('.room_direct_model').show();
                $('#downloadAlert').hide();
            } else {
                $('.room_direct_model').hide();
                $('#downloadAlert').show();
            }

            //如果用户不是文件夹的拥有者，则显示出加入收藏夹的按钮
            if (this.room.owner == 0) {
                $('#room_btn_favorate').on('click', () => {
                    this.favoriteAdd(rsp.data.mr_id);
                });
                $('#room_btn_favorate').show();
            }

            //如果用户不是文件夹的拥有者，则显示举报按钮
            if (this.room.owner == 0) {
                $('#room_btn_report').show();
            }

            //如果这个文件夹有人收藏，则显示出收藏数量
            if (rsp.data.favorites > 0) {
                $('.fav-enabled').show();
                $('#favorite_count').html(rsp.data.favorites);
            }

            //如果文件夹不是用户的，则隐藏偏好设定
            if (this.room.owner == 0) {
                $('.room_btn_performance').hide();
            }

            //如果文件夹有设置图片
            if (this.room.img_link != '0') {
                //设置占位图
                $('.room_img').attr('src', '/img/loading.svg');
                //先请求图片，就绪后再显示
                let img = new Image();
                img.src = this.room.img_link;
                img.onload = () => {
                    $('.room_img').attr('src', this.room.img_link);
                }
                $('.room_img').show();
                //调整 UI
                $('#dir_title').attr('class','col-8');
                $('#dir_img').show();
            } else {
                $('.room_img').hide();
                //调整 UI
                $('#dir_title').attr('class','col-12');
                $('#dir_img').hide();
            }

            //如果是私有文件夹
            if (this.room.model == 'private') {
                $('.in-private-dir').hide();
                this.setDirIcon('private');
            } else {
                $('.in-private-dir').show();
                this.setDirIcon('public');
            }

            //如果文件夹允许其他人上传文件
            if (this.room.allow_upload == 'yes') {
                $('#pf_allow_upload').prop('checked', true);
            } else {
                $('#pf_allow_upload').prop('checked', false);
            }

            //如果是公开文件夹，启用搜索
            if (this.room.publish === 'yes') {
                $('#pf_publish').prop('checked', true);
                this.setDirIcon('publish');
            } else {
                $('#pf_publish').prop('checked', false);
                this.setDirIcon('public');
            }

            //如果有设定个性化设置
            if (this.room.ui_publish === 'yes' && this.room.ui_publish_status === 'ok') {
                if (this.room.ui_pro === 'yes') {
                    $('.userinfo_pro').show();
                } else {
                    $('.userinfo_sd').show();
                }
                $('.userinfo').show();
                $('.userinfo_nickname').html(`${this.room.ui_nickname}`);
            }


            $('#mr_copy').attr('data-clipboard-text', 'https://' + this.parent_op.site_domain + '/room/' + rsp.data.mr_id);
            $('.room_title').html(rsp.data.name);
            $('#dir_list').show();

            if (rsp.data.sub_rooms !== 0) {
                this.subroom_data = rsp.data.sub_rooms;
            } else {
                this.subroom_data = 0;
            }

            this.parent_op.btn_copy_bind();
            this.filelist(0);

            //是否需要设置上级目录返回按钮
            if (this.room.top == 99) {
                $('.btn_for_sub').hide();
                $('.btn_for_desktop').show();
            } else {
                $('.btn_for_sub').show();
                $('.btn_for_desktop').hide();
            }

            //如果不是拥有者
            if (this.room.owner === 0) {
                $('.not_owner').hide();
            }

            if (isMobileScreen()) {
                this.mobilePrepare();
            } else {
                $('#room_back_btn').html(app.tpl('room_back_btn_tpl', {}));
            }

            //如果是赞助者，激活特定按钮的颜色
            if (this.parent_op.sponsor) {
                this.parent_op.isSponsor = true;
                this.parent_op.setBtnForSponsor();
            }

            $('#room_loading').hide();
            $('#room_loaded').show();

            //重新设定网页标题
            document.title = rsp.data.name;
            app.linkRebind();
        });
    }

    setDirIcon(status){
        //默认
        $('#dir_status').attr('name', 'folder-open-e1ad2j7l');
        if(status==='publish'){
            $('#dir_status').attr('name', 'folder-conversion-one');
        }
        if(status==='private'){
            $('#dir_status').attr('name', 'folder-lock-one');
        }
    }

    getIcons(room){
        let re = {icon:'',color:''};
        if(room.model === 'private'){
            re.icon = 'folder-lock-one';
            re.color = 'text-success';
            return re;
        }
        if(room.publish === 'yes'){
            re.icon = 'folder-conversion-one';
            re.color = 'text-yellow';
            return re;
        }
        if(room.fav !== 0){
            re.icon = 'folder-focus-one';
            re.color = 'text-pink';
            return re;
        }
        re.icon = 'folder-open-e1ad2j7l';
        re.color = 'text-yellow';
        return re;
    }

    mobilePrepare() {
        let mrid = this.room.mr_id === undefined ? 0 : this.room.mr_id;
        if (mrid !== 0) {
            let back_btn = `<a href="/app&listview=room&mrid=${this.room.parent}" tmpui-action="TL.dir.open()" class="text-azure mt-1 btn_for_sub"><iconpark-icon name="left-c" class="fa-fw fa-2x"></iconpark-icon></a>`;
            $('#room_back').html(back_btn);
        } else {
            $('#room_back').html('');
        }

        $('.btn_upload').attr('onclick', `TL.uploader.open('${mrid}')`);

        $('#mr_id').val(mrid);
        $('#mr_parent_id').val(this.room.parent);
        $('#mr_top_id').val(this.room.top);

        app.linkRebind();
        this.mobileTopabrFix(mrid);
    }

    mobileTopabrFix(mrid) {
        if (mrid === 0) {
            $('.mobile-head-padding-large').css('padding-top', '80px');
            $('.btn_mobile_top').hide();
            $('.btn_mobile_sub').show();
        } else {
            $('.btn_mobile_top').show();
            $('.btn_mobile_sub').hide();
            //根据 room_subinfo 的显示状态来设定 padding-top 的值
            if ($('.room_subinfo').css('display') === 'none') {
                $('.mobile-head-padding-large').css('padding-top', '150px');
            } else {
                $('.mobile-head-padding-large').css('padding-top', '170px');
            }
        }
    }

    favoriteAdd(mr_id) {
        if (!this.parent_op.isLogin()) {
            app.open('/app&listview=login');
            return false;
        }
        alert(app.languageData.favorite_add_success);
        $.post(this.parent_op.api_mr, {
            action: 'favorite_add',
            token: this.parent_op.api_token,
            mr_id: mr_id,
        });
    }

    favoriteDel(mr_id) {
        $('#meetingroom_id_' + mr_id).hide();
        $.post(this.parent_op.api_mr, {
            action: 'favorite_del',
            token: this.parent_op.api_token,
            mr_id: mr_id,
        });
    }

    fileAdd(ukey) {
        var params = get_url_params();
        $('#btn-mraddlist-' + ukey).fadeOut(300);
        this.parent_op.recaptcha_do('mr_add', (recaptcha) => {
            $.post(this.parent_op.api_mr, {
                action: 'file_add',
                token: this.parent_op.api_token,
                //captcha: recaptcha,
                mr_id: params.mrid,
                ukey: ukey
            }, (rsp) => {
                $('#mraddlist-' + ukey).fadeOut(500);
            });
        });
    }

    filelist(page) {
        $('.no_files').fadeOut();
        $('.no_dir').fadeOut();
        $('.no_photos').fadeOut();

        $('#dir_list').html('');
        this.parent_op.list_data = [];

        //清空数据
        //$('#dir_list').html('');

        //if search
        let search = $('#room_search').val();

        $('#dir_list_box').show();
        $('.mr_filelist_refresh_icon').addClass('fa-spin');
        $('.mr_filelist_refresh_icon').attr('disabled', true);
        this.loadingON();
        var params = get_url_params();


        //获取文件夹关于排序的设定
        let key = getSortKeys();
        let room_sort_by = localStorage.getItem(key.sort_by);
        let room_sort_type = localStorage.getItem(key.sort_type);
        let room_display = localStorage.getItem(key.display);

        this.parent_op.recaptcha_do('mr_list', (recaptcha) => {
            let photo = 0;
            if (room_display == 'photo') {
                photo = 1;
            }
            $.post(this.parent_op.api_mr, {
                action: 'file_list_page',
                token: this.parent_op.api_token,
                //captcha: recaptcha,
                page: 0,
                photo: photo,
                mr_id: params.mrid,
                sort_by: room_sort_by,
                sort_type: room_sort_type,
                search: search
            }, (rsp) => {
                //重要，装填用于提供下载的数据
                this.parent_op.list_data = listDataPrepare(rsp.data);
                $('.data_loading').hide();
                $('.mr_filelist_refresh_icon').removeClass('fa-spin');
                $('.mr_filelist_refresh_icon').removeAttr('disabled');
                this.listModel(rsp.data, page, params.mrid);
                this.parent_op.dir_list_autoload_disabled();
                this.parent_op.autoload = false;
                this.file_list = rsp.data;
                this.loadingOFF();
            });
        });
    }

    performanceInit(display,sort_by,sort_type) {
        //先检查这个文件夹是否已经有排序设定
        let keys = getSortKeys();

        let r_display = localStorage.getItem(keys.display);
        let r_sort_by = localStorage.getItem(keys.sort_by);
        let r_sort_type = localStorage.getItem(keys.sort_type);

        //初始化远端设定的选定值
        $('#pf_display').val(display);
        $('#pf_sort_by').val(sort_by);
        $('#pf_sort_type').val(sort_type);

        //如果本地没有存储，则使用文件夹的远端设定
        if (r_display === null) {
            localStorage.setItem(keys.display, display);
        }
        if (r_sort_by === null) {
            localStorage.setItem(keys.sort_by, sort_by);
            r_sort_by = sort_by;
        }
        if (r_sort_type === null) {
            localStorage.setItem(keys.sort_type, sort_type);
            r_sort_type = sort_type;
        }

        //初始化本地存储的选定值
        $('#sort_by').val(r_sort_by);
        $('#sort_type').val(r_sort_type);
    }

    performanceOpen() {
        $('#performanceModal').modal('show');
    }

    /**
     * 保存用户的设定   
     */
    performancePost() {
        let pf_display = $('#pf_display').val();
        let pf_sort_by = $('#pf_sort_by').val();
        let pf_sort_type = $('#pf_sort_type').val();
        let pf_publish   = $('#pf_publish').is(':checked') ? 'yes' : 'no';
        let pf_allow_upload = $('#pf_allow_upload').is(':checked') ? 'yes' : 'no';
        let mrid = this.room.mr_id;
        $.post(this.parent_op.api_mr, {
            action: 'pf_set',
            token: this.parent_op.api_token,
            pf_display: pf_display,
            sort_by: pf_sort_by,
            sort_type: pf_sort_type,
            pf_upload: pf_allow_upload,
            pf_publish: pf_publish,
            mr_id: mrid
        });
    }

    btnActiveReset() {
        $('#room_btn_file_list').removeClass('text-blue');
        $('#room_btn_file_grid').removeClass('text-blue');
        $('#room_btn_file_photo').removeClass('text-blue');
    }

    treeGet() {
        $.post(this.parent_op.api_mr, {
            action: 'get_dir_tree',
            token: this.parent_op.api_token
        }, (rsp) => {
            if (rsp.status === 1) {
                this.dir_tree = rsp.data;
            } else {
                $('#mv_box_0').html(app.languageData.status_error_14);
            }
        });
    }

    treeShow(parent) {
        for (let i in this.dir_tree) {
            if (this.treeHaveChildren(this.dir_tree[i].id)) {
                this.dir_tree[i].children = true;
            } else {
                this.dir_tree[i].children = false;
            }
            if (this.dir_tree[i].parent == parent) {
                $('#mv_box_' + parent).append(app.tpl('mv_box_tpl', this.dir_tree[i]));
                $('#mv_box_' + parent).slideDown();
                $('#mv_select_box_' + parent).removeAttr('onclick');
            }
        }
    }

    treeHaveChildren(parent) {
        for (let i in this.dir_tree) {
            if (this.dir_tree[i].parent == parent) {
                return true;
            }
        }
        return false;
    }

    moveTo(data, place) {
        let target = $("input[name='dir_tree']:checked").val();
        if (target === undefined) {
            alert(this.language_get.status_error_13);
            return false;
        }
        $.post(this.parent_op.api_mr, {
            action: 'move_to_dir2',
            token: this.parent_op.api_token,
            data: data,
            mr_id: target
        }, (rsp) => {
            $('#movefileModal').modal('hide');
            if (place == 'workspace') {
                this.parent_op.workspace_filelist(0);
            } else {
                this.open();
            }
        });
    }

    loadingON() {
        $('#loading_box').show();
    }

    loadingOFF() {
        $('#loading_box').fadeOut();
    }
}