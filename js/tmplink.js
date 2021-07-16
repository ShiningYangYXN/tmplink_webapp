class tmplink {

    api_url = 'https://connect.tmp.link/api_v2'
    api_url_upload = this.api_url + '/file'
    api_file = this.api_url + '/file'
    api_user = this.api_url + '/user'
    api_mr = this.api_url + '/meetingroom'
    api_toks = this.api_url + '/token'
    api_token = null
    upload_queue_id = 0
    upload_queue_file = []
    upload_processing = 0
    logined = 0
    uid = 0
    email = null
    api_language = null
    languageData = {}
    mr_data = []
    room = []
    room_data = []
    list_data = []
    dir_tree = {}
    subroom_data = []
    recaptcha = '6LfqxcsUAAAAABAABxf4sIs8CnHLWZO4XDvRJyN5'
    download_queue = []
    download_queue_processing = false
    download_index = 0
    lazyLoadInstance = null
    get_details_do = false
    upload_s2_status = []
    storage = 0
    storage_used = 0
    page_number = 1
    autoload = false
    sort_by = 0
    sort_type = 0
    single_file_size = 10 * 1024 * 1024 * 1024
    file_manager = null
    upload_model_selected_val = 0
    download_retry = 0
    download_retry_max = 10

    constructor() {
        this.app_init();
        this.api_init();
        //初始化管理器
        this.file_manager = new tools_file_manager;
        this.file_manager.init(this);
        this.upload_model_selected_val = localStorage.getItem('app_upload_model') === null ? 0 : localStorage.getItem('app_upload_model');

        var token = localStorage.getItem('app_token');
        this.recaptcha_do('init', (captcha) => {
            $.post(this.api_toks, {
                'action': 'token_check',
                'captcha': captcha,
                token: token
            }, (rsp) => {
                if (rsp.status == 3) {
                    //init fail
                    let html = app.tpl('initFail', {});
                    $('#tmpui_body').html(html);
                    return false;
                }
                if (rsp.status != 1) {
                    this.recaptcha_do('init', (captcha) => {
                        $.post(this.api_toks, {
                            'action': 'token',
                            'captcha': captcha,
                            token: token
                        }, (rsp) => {
                            this.api_token = rsp.data;
                            localStorage.setItem('app_token', rsp.data);
                            this.details_init();
                        });
                    });
                } else {
                    this.api_token = token;
                    this.details_init();
                }
            });
        });

        app.ready(() => {
            this.lazyLoadInstance = new LazyLoad({
                elements_selector: ".lazyload"
            });
        });

        $(document).on({
            dragleave: function (e) {
                e.preventDefault();
            },
            drop: function (e) {
                e.preventDefault();
            },
            dragenter: function (e) {
                e.preventDefault();
            },
            dragover: function (e) {
                e.preventDefault();
            }
        });
    }

    languageData_init(lang) {
        this.languageData = lang;
    }

    bg_load() {
        let bglist = [1, 2, 3, 4, 5];
        let index = Math.floor((Math.random() * bglist.length));
        let img = new Image();
        //img.src = '/img/bg/core/'+bglist[index]+'.jpg';
        img.src = '/img/bg/s3.jpg';
        img.onload = () => {
            if (img.height >= 1080 && img.width >= 1920) {
                $('body').append('<div id="background_wrap" style="z-index: -1;position: fixed;top: 0;left: 0;height: 100%;width: 100%;background-size: cover;background-repeat: no-repeat;background-attachment: scroll;background-image:url(' + img.src + ');"></div>');
            }
        }
    }

    app_init() {
        let sort_by = localStorage.getItem('app_sort_by');
        let sort_type = localStorage.getItem('app_sort_by');

        this.sort_by = sort_by === null ? 0 : sort_by;
        this.sort_type = sort_type === null ? 0 : sort_type;

        this.bg_load();
    }

    details_init() {
        var login = localStorage.getItem('app_login');
        if (login != null && login != 0) {
            this.logined = 1;
        } else {
            this.logined = 0;
        }
        this.get_details(() => {
            this.get_details_do = true;
            this.head_set();
        });
    }

    head_set_refresh() {
        if (this.get_details_do) {
            this.head_set();
        }
    }

    isLogin() {
        if (localStorage.getItem('app_login') == 1) {
            return true;
        } else {
            return false;
        }
    }


    upload_model_selected(model) {
        console.log('upload::model::' + model);
        switch (model) {
            case 0:
                $('.current_selected').html(this.languageData.modal_settings_upload_model1);
                $('#upload_model').val(0);
                break;
            case 1:
                $('.current_selected').html(this.languageData.modal_settings_upload_model2);
                $('#upload_model').val(1);
                break;
            case 2:
                $('.current_selected').html(this.languageData.modal_settings_upload_model3);
                $('#upload_model').val(2);
                break;
            case 3:
                $('.current_selected').html(this.languageData.modal_settings_upload_model3);
                $('#upload_model').val(4);
                break;
            case 99:
                $('.current_selected').html(this.languageData.modal_settings_upload_model99);
                $('#upload_model').val(99);
                break;
        }
        localStorage.setItem('app_upload_model', model);
    }

    dir_tree_get() {
        $.post(this.api_mr, {
            action: 'get_dir_tree',
            token: this.api_token
        }, (rsp) => {
            if (rsp.status === 1) {
                this.dir_tree = rsp.data;
            } else {
                $('#mv_box_0').html(this.languageData.status_error_14);
            }
        });
    }

    dir_tree_display(parent) {
        for (let i in this.dir_tree) {
            if (this.dir_tree_have_children(this.dir_tree[i].id)) {
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

    dir_tree_have_children(parent) {
        for (let i in this.dir_tree) {
            if (this.dir_tree[i].parent == parent) {
                return true;
            }
        }
        return false;
    }

    move_to_dir(ukey, place) {
        let target = $("input[name='dir_tree']:checked").val();
        if (target === undefined) {
            alert(this.language_get.status_error_13);
            return false;
        }
        $.post(this.api_mr, {
            action: 'move_to_dir',
            token: this.api_token,
            ukey: ukey,
            mr_id: target
        }, (rsp) => {
            $('#movefileModal').modal('hide');
            if (place == 'workspace') {
                this.workspace_filelist(0);
            } else {
                this.mr_file_list(0);
            }
        });
    }

    get_file() {
        let code = $('#get_file').val();
        if (code.length !== 13) {
            this.alert(this.language_get.status_error_15);
            return false;
        }
        window.open('http://tmp.link/f/' + code);
    }

    loading_box_on() {
        $('#loading_box').fadeIn();
    }

    loading_box_off() {
        $('#loading_box').fadeOut();
    }

    recaptcha_do(type, cb) {
        if (type !== 'init') {
            if (this.api_token === null) {
                setTimeout(() => {
                    this.recaptcha_do(type, cb);
                }, 500);
                return false;
            } else {
                cb(Math.floor(Math.random() * 10));
                return true;
            }
        }
        cb(this.randomString(32));
        return true;
        if (typeof grecaptcha === 'object') {
            grecaptcha.ready(() => {
                grecaptcha.execute(this.recaptcha, {
                    action: type
                }).then((token) => {
                    cb(token);
                });
            });
        } else {
            setTimeout(() => {
                this.recaptcha_do(type, cb);
            }, 500);
        }
    }

    sort_show() {
        $("#sort_by option[value='" + this.sort_by + "']").attr("selected", "selected");
        $("#sort_type option[value='" + this.sort_type + "']").attr("selected", "selected");
        $('#sortModal').modal('show');
    }

    sort_confirm() {
        this.sort_by = $('#sort_by').val();
        this.sort_type = $('#sort_type').val();
        localStorage.setItem("app_sort_by", this.sort_by);
        localStorage.setItem("app_sort_type", this.sort_type);
        $('#sortModal').modal('hide');
    }

    head_set() {
        var login = localStorage.getItem('app_login');
        if (login != null && login != 0) {
            this.logined = 1;
            $('.workspace-navbar').show();
            $('.workspace-nologin').hide();
        } else {
            $('.workspace-navbar').hide();
            $('.workspace-nologin').show();
        }
        $('.navbar_nloading').hide();
        $('.navbar_ready').show();
    }

    get_details(cb) {
        $.post(this.api_user, {
            action: 'get_detail',
            token: this.api_token
        }, (rsp) => {
            if (rsp.status === 1) {
                localStorage.setItem('app_login', 1);
                this.logined = 1;
                this.storage_used = rsp.data.storage_used;
                this.storage = rsp.data.storage;
                localStorage.setItem('app_lang', rsp.data.lang);
                app.languageSet(rsp.data.lang);
                //console.log
                this.dir_tree_get();
            } else {
                localStorage.setItem('app_login', 0);
                this.logined = 0;
            }
            cb();
        });
    }

    password_reset_confim() {
        var password = $('#modal_password_reset').val();
        var rpassword = $('#modal_password_reset_re').val();
        if (password !== rpassword) {
            $("#notice_resetpassword").html(this.languageData.model_resetpassword_error_no_match);
            return false;
        }
        $("#notice_resetpassword").html(this.languageData.model_resetpassword_msg_processing);
        $("#modal_password_reset_btn").attr('disabled', true);
        $.post(this.api_user, {
            action: 'passwordreset',
            password: password,
            rpassword: rpassword,
            token: this.api_token
        }, (rsp) => {
            if (rsp.status === 1) {
                $("#notice_resetpassword").html(this.languageData.model_resetpassword_msg_processed);
                $("#modal_password_reset_btn").html(this.languageData.model_resetpassword_msg_processed);
            } else {
                $("#notice_resetpassword").html(this.languageData.model_resetpassword_error_fail);
                $("#modal_password_reset_btn").removeAttr('disabled');
            }
        });
    }

    email_change_confim() {
        var email = $('#email').val();
        var code = $('#checkcode').val();
        $("#notice_emailchange").html(this.languageData.model_email_change_msg_processing);
        $("#email_change_confim_btn").attr('disabled', true);
        $.post(this.api_user, {
            action: 'email_change',
            email: email,
            code: code,
            token: this.api_token
        }, (rsp) => {
            if (rsp.status === 1) {
                $("#notice_emailchange").html(this.languageData.model_email_change_msg_processed);
                $("#email_change_confim_btn").html(this.languageData.model_email_change_msg_processed);
            } else {
                $("#notice_emailchange").html(rsp.data);
                $("#email_change_confim_btn").removeAttr('disabled');
            }
        });
    }

    previewModel(ukey, id) {
        let url = 'https://tmplinkapp-connect.vx-cdn.com/img-' + ukey + '-0x0.jpg';
        $('#preview_img').attr('src', '/img/lazy.gif');
        $.get(url, () => {
            $('#preview_img').attr('src', url);
        });
        let lastukey = $('#btn_preview_download').attr('data-ukey');
        $('#btn_preview_download').removeClass('btn_download_' + lastukey);
        $('#preview_download_1').removeClass('download_progress_bar_' + lastukey);
        $('#preview_download_2').removeClass('download_progress_bar_set_' + lastukey);
        $('#btn_preview_download').addClass('btn_download_' + ukey);
        $('#preview_download_1').addClass('download_progress_bar_' + ukey);
        $('#preview_download_2').addClass('download_progress_bar_set_' + ukey);
        $('#btn_preview_download').attr('data-ukey', ukey);

        $('#btn_preview_download').removeAttr('disabled');
        $('#btn_preview_download').html(this.languageData.on_select_download);
        $('#btn_preview_download').attr('onclick', 'TL.download_file_btn(\'' + ukey + '\')');
        $('#btn_preview_remove').attr('onclick', "TL.workspace_del('" + ukey + "')");
        $('#previewModal').modal('show');
    }

    password_found() {
        this.recaptcha_do('init', (captcha) => {
            var email = $('#email').val();
            if (email === '') {
                return false;
            }
            $('#submit').attr('disabled', true);
            $('#msg_notice').fadeIn();
            $('#msg_notice').html(this.languageData.form_btn_processing);
            $.post(this.api_user, {
                action: 'passwordfound',
                token: this.api_token,
                email: email,
                captcha: captcha
            }, (rsp) => {
                if (rsp.status == 1) {
                    $('#msg_notice').fadeOut();
                    $('#submit').html(this.languageData.form_btn_processed);
                } else {
                    switch (rsp.status) {
                        case 13:
                            $('#msg_notice').html(this.languageData.status_13);
                            break;
                        case 14:
                            $('#msg_notice').html(this.languageData.status_14);
                            break;
                        default:
                            $('#msg_notice').html(this.languageData.status_unknow);
                    }
                    $('#submit').removeAttr('disabled');
                }
            }, 'json');
        });
    }

    workspace_navbar() {
        if (localStorage.getItem('app_login') == 1) {
            $('.workspace-navbar').show();
        }
    }

    workspace_add(ukey) {
        $('#btn_add_to_workspace').addClass('disabled');
        $.post(this.api_file, {
            action: 'add_to_workspace',
            token: this.api_token,
            ukey: ukey
        }, (rsp) => {
            $('#btn_add_to_workspace').html('<i class="fas fa-check-circle" aria-hidden="true"></i>');
        }, 'json');
    }

    workspace_del(ukey) {
        $('#file_unit_' + ukey).hide();
        $.post(this.api_file, {
            action: 'remove_from_workspace',
            token: this.api_token,
            ukey: ukey
        }, (rsp) => {
            // $('#btn_add_to_workspace').html('<i class="fas fa-check-circle" aria-hidden="true"></i>');
            // $('#file_unit_' + ukey).fadeOut();
            //this.workspace_filelist();
        }, 'json');
    }

    workspace_filelist_autoload_enabled() {
        this.autoload = true;
        $(window).on("scroll", (event) => {
            if ($(event.currentTarget).scrollTop() + $(window).height() + 100 >= $(document).height() && $(event.currentTarget).scrollTop() > 100) {
                if (this.autoload == true) {
                    this.autoload = false;
                    this.workspace_filelist(1);
                }
            }
        });
    }

    workspace_filelist_autoload_disabled() {
        $(window).off("scroll");
    }

    workspace_filelist(page) {
        $('.no_files').fadeOut();
        $('.no_photos').fadeOut();
        //when page is 0,page will be init
        if (page == 0) {
            this.page_number = 0;
            $('#workspace_filelist').html('');
            this.list_data = [];
        } else {
            this.page_number++;
        }
        if (localStorage.getItem('app_login') != 1) {
            this.logout();
            return false;
        }
        //if search
        let search = $('#workspace_search').val();

        $('#filelist_refresh_icon').addClass('fa-spin');
        $('#filelist_refresh_icon').attr('disabled', true);
        this.loading_box_on();
        this.recaptcha_do('workspace_list', (recaptcha) => {
            let photo = 0;
            if (localStorage.getItem('app_workspace_view') == 'photo') {
                photo = 1;
            }
            $.post(this.api_file, {
                action: 'workspace_filelist_page',
                page: this.page_number,
                token: this.api_token,
                sort_type: this.sort_type,
                sort_by: this.sort_by,
                photo: photo,
                search: search
            }, (rsp) => {
                $('#filelist_refresh_icon').removeClass('fa-spin');
                $('#filelist_refresh_icon').removeAttr('disabled');
                if (rsp.status === 0) {
                    if (page == 0) {
                        $('#workspace_filelist').html('<div class="text-center"><i class="fa-fw fad fa-folder-open fa-4x"></i></div>');
                    }
                    this.autoload = false;
                } else {
                    this.workspace_view(rsp.data, page);
                    this.autoload = true;
                    for (let i in rsp.data) {
                        this.list_data[rsp.data[i].ukey] = rsp.data[i];
                    }
                }
                $('#filelist').fadeIn();
                this.loading_box_off();
                //cancel
                if (rsp.status == 0 || rsp.data.length < 50) {
                    this.room_filelist_autoload_disabled();
                }
            });
        });
    }

    workspace_filelist_model(type) {
        switch (type) {
            case 'photo':
                localStorage.setItem('app_workspace_view', 'photo');
                break;
            case 'list':
                localStorage.setItem('app_workspace_view', 'list');
                break;
            default:
                localStorage.setItem('app_workspace_view', 'list');
        }
        this.workspace_filelist(0);
    }

    workspace_view(data, page) {
        switch (localStorage.getItem('app_workspace_view')) {
            case 'photo':
                this.workspace_filelist_by_photo(data, page);
                break;
            case 'list':
                this.workspace_filelist_by_list(data, page);
                break;
            default:
                this.workspace_filelist_by_list(data, page);
        }
    }

    workspace_btn_active_reset() {
        $('#ws_btn_file_list').removeClass('bg-dark');
        $('#ws_btn_file_grid').removeClass('bg-dark');
        $('#ws_btn_file_photo').removeClass('bg-dark');
    }

    workspace_filelist_by_photo(data, page) {
        this.workspace_btn_active_reset();
        $('#ws_btn_file_photo').addClass('bg-dark');
        if (page == 0 && data == false) {
            $('.no_photos').fadeIn();
        }
        if (data.length == 0) {
            return false;
        }
        if (page == 0) {
            $('#workspace_filelist').html('<div class="row" id="filelist_photo"></div>');
        }
        $('#filelist_photo').append(app.tpl('workspace_filelist_photo_tpl', data));
        this.btn_copy_bind();
        app.linkRebind();
        this.lazyLoadInstance.update();
    }

    workspace_filelist_by_list(data, page) {
        this.workspace_btn_active_reset();
        $('#ws_btn_file_list').addClass('bg-dark');
        if (page == 0 && data == false) {
            $('.no_files').fadeIn();
        }
        if (data.length == 0) {
            return false;
        }
        $('#workspace_filelist').append(app.tpl('workspace_filelist_list_tpl', data));
        this.btn_copy_bind();
        app.linkRebind();
    }

    file_model_change(ukey, model) {
        this.loading_box_on();
        this.recaptcha_do('file', (recaptcha) => {
            $.post(this.api_file, {
                action: 'change_model',
                ukey: ukey,
                //captcha: recaptcha,
                token: this.api_token,
                model: model
            }, (rsp) => {
                if (rsp.status === 1) {

                    return true;
                }
                this.loading_box_off();
            }, 'json');
        });
    }

    details_file() {
        // if (this.isWeixin()) {
        //     $('#file_messenger_icon').html('<i class="fad fa-download fa-fw fa-4x"></i>');
        //     $('#file_messenger_msg').removeClass('display-4');
        //     $('#file_messenger_msg').html('由于微信的限制，目前无法提供下载。请复制链接后，在外部浏览器打开进行下载。');
        //     $('#file_messenger').show();

        //     gtag('config', 'UA-96864664-3', {
        //         'page_title': 'D-weixinUnavailable',
        //     });
        //     return false;
        // }
        this.loading_box_on();
        this.recaptcha_do('file', (recaptcha) => {
            var params = this.get_url_params();
            if (params.ukey !== undefined) {
                $.post(this.api_file, {
                    action: 'details',
                    ukey: params.ukey,
                    //captcha: recaptcha,
                    token: this.api_token
                }, (rsp) => {
                    if (rsp.status === 1) {
                        gtag('config', 'UA-96864664-3', {
                            'page_title': 'D-' + rsp.data.name,
                        });
                        $('#file_box').fadeIn();
                        $('#filename').html(rsp.data.name);
                        $('#filesize').html(rsp.data.size);
                        $('#btn_add_to_workspace').on('click', () => {
                            if (this.logined == 1) {
                                this.workspace_add(params.ukey);
                            } else {
                                app.open('/login');
                            }
                        });
                        $('#btn_download').attr('x-href', 'https://tmplinkapp-connect.vx-cdn.com/connect-' + this.api_token + '-' + params.ukey);
                        $('#btn_highdownload').attr('x-href', 'https://tmplinkapp-connect.vx-cdn.com/connect-' + this.api_token + '-' + params.ukey);
                        $('.single_download_progress_bar').attr('data-href', 'https://tmplinkapp-connect.vx-cdn.com/connect-' + this.api_token + '-' + params.ukey);
                        $('.single_download_progress_bar').attr('data-filename', rsp.data.name);
                        $('.btn_copy_fileurl').attr('data-clipboard-text', 'http://tmp.link/f/' + params.ukey);
                        $('#file_ukey').attr('data-clipboard-text', params.ukey);
                        $('#file_btn_clidownload').attr('data-clipboard-text', 'https://tmplinkapp-connect.vx-cdn.com/connect-' + this.api_token + '-' + params.ukey);
                        $('#qr_code_url').attr('src', this.api_url + '/qr?code=' + params.ukey);
                        $('#report_ukey').html(params.ukey);
                        this.btn_copy_bind();
                        if (this.logined) {
                            $('.user-nologin').hide();
                            $('.user-login').show();
                        } else {
                            $('.user-nologin').show();
                            $('.user-login').hide();
                        }
                        //this.btn_copy_bind();
                        // if (rsp.data.type == 'jpg' || rsp.data.type == 'jpeg' || rsp.data.type == 'png' || rsp.data.type == 'gif') {
                        //     let img_url = 'https://tmplinkapp-connect.vx-cdn.com/img-' + params.ukey + '-0x0.jpg';
                        //     $('.img_great').attr('src', img_url);
                        //     //specail image model
                        //     let img = new Image();
                        //     img.src = img_url;
                        //     img.onload = () => {
                        //         if (img.height >= 1080 && img.width >= 1920) {
                        //             $('.img_great').fadeOut();
                        //             $('body').css('background-image', 'url(' + img_url + ')');
                        //             $('body').css('background-size', '100% auto');
                        //         }
                        //     }
                        // }
                        return true;
                    }

                    //file need to login
                    if (rsp.status === 3) {
                        $('#file_messenger_icon').html('<i class="fad fa-sign-in fa-fw fa-4x"></i>');
                        $('#file_messenger_msg').html(this.languageData.status_need_login);
                        $('#file_messenger').show();
                        gtag('config', 'UA-96864664-3', {
                            'page_title': 'D-unLogin',
                        });
                        return false;
                    }

                    //file unavailable
                    $('#file_messenger_icon').html('<i class="fas fa-folder-times  fa-4x"></i>');
                    $('#file_messenger_msg').html(this.languageData.file_unavailable);
                    $('#file_messenger').show();
                    gtag('config', 'UA-96864664-3', {
                        'page_title': 'D-fileUnavailable',
                    });
                }, 'json');
            } else {
                $('#file_unavailable').fadeIn();
            }
            this.loading_box_off();
        });
    }

    single_download_start(url, filename) {
        var xhr = new XMLHttpRequest();
        xhr.addEventListener("progress", (evt) => {
            this.single_download_progress_on(evt, filename);
        }, false);
        xhr.addEventListener("error", (evt) => {
            if (this.download_retry < this.download_retry_max) {
                this.download_retry++;
                setTimeout(() => {
                    this.single_download_start(url, filename);
                }, 3000);
            } else {
                this.alert('下载发生错误，请重试。');
                this.single_download_reset();
                //reset download retry
                this.download_retry = 0;
            }
        }, false);
        xhr.addEventListener("abort", (evt) => {
            this.alert('下载中断，请重试。');
            this.single_download_reset();
        }, false);
        xhr.open("GET", url);
        xhr.onload = () => {
            this.single_download_complete(xhr, filename);
        };
        xhr.responseType = 'blob';
        xhr.send();
        $('.single_download_msg').html('准备中，正在开始下载...');
        $('.single_download_progress_bar').fadeIn();
        $('#btn_download').attr('disabled', true);
        $('#file_btn_highdownload').attr('disabled', true);
    }

    single_download_complete(evt, filename) {
        this.download_retry = 0;
        let blob = new Blob([evt.response], {
            type: evt.response.type
        });
        //ie的下载
        if (window.navigator.msSaveOrOpenBlob) {
            navigator.msSaveBlob(blob, filename);
        } else {
            //非ie的下载
            let link = document.createElement('a');
            link.href = window.URL.createObjectURL(blob);
            link.download = filename;
            link.click();
            window.URL.revokeObjectURL(link.href);
        }
        //恢复进度条样式
        $('.single_download_msg').html('下载完成.');
        $('.single_download_progress_bar_set').removeClass('progress-bar-animated');
        $('.single_download_progress_bar_set').removeClass('progress-bar-striped');
        this.single_download_reset();
        this.download_queue_run();
    }

    single_download_progress_on(evt) {
        $('.single_download_msg').html('已下载... ' + this.bytetoconver(evt.loaded, true));
        $('.single_download_progress_bar_set').css('width', (evt.loaded / evt.total) * 100 + '%');
        $('.single_download_progress_bar_set').addClass('progress-bar-animated');
        $('.single_download_progress_bar_set').addClass('progress-bar-striped');
    }

    single_download_reset() {
        $('#btn_download').removeAttr('disabled');
        $('#file_btn_highdownload').removeAttr('disabled');
    }

    isWeixin() {
        var ua = navigator.userAgent.toLowerCase();
        return ua.match(/MicroMessenger/i) == "micromessenger";
    }

    isMobile() {
        if (/(iphone|ipad|ipod|ios|android)/i.test(navigator.userAgent.toLowerCase())) {
            return true;
        } else {
            return false;
        };
    }

    download_check() {
        // if (this.isWeixin()) {
        //     return false;
        // }
        // if (this.isMobile()) {
        //     return false;
        // }
    }

    download_queue_add(url, filename, ukey, filesize, filetype) {
        // if (this.isWeixin()) {
        //     this.alert(TL.languageData.file_not_allow_in_wechat);
        //     return false;
        // }
        // if (this.isMobile()) {
        //     window.open(url, '_blank');
        //     return false;
        // }
        this.download_queue[ukey] = [url, filename, ukey, ukey];
        // let html = app.tpl('download_list_tpl', {
        //     index: ukey,
        //     fname: filename,
        //     ftype: filetype,
        //     fsize_formated: filesize
        // });
        // $('#download_queue_list').prepend(html);
    }

    download_queue_del(index) {
        //$('#download_task_' + index).fadeOut();
        //移除下载，todo
        delete this.download_queue[index];
        this.download_queue_run();
    }

    download_queue_start() {
        this.download_queue_run();
    }

    download_queue_run() {
        if (this.download_queue_processing) {
            return false;
        }
        for (let x in this.download_queue) {
            let data = this.download_queue[x];
            if (data !== undefined) {
                console.log("Downloading:" + data[0]);
                this.download_queue_processing = true;
                this.download_queue_progress_start(data[0], data[1], data[2], data[3]);
                // $('#download_queue').fadeIn();
                return true;
            } else {
                // $('#download_queue').fadeOut();
                console.log('Queue out.');
            }
        }
        $('#download_queue').fadeOut();
    }

    download_queue_progress_start(url, filename, id, index) {
        var xhr = new XMLHttpRequest();
        xhr.addEventListener("progress", (evt) => {
            this.download_progress_on(evt, id, filename, index);
        }, false);
        xhr.addEventListener("load", (evt) => {
            delete this.download_queue[index];
            this.download_queue_start();
        }, false);
        xhr.addEventListener("error", (evt) => {
            if (this.download_retry < this.download_retry_max) {
                this.download_retry++;
                setTimeout(() => {
                    this.download_queue_progress_start(url, filename, id, index);
                }, 3000);

            } else {
                delete this.download_queue[index];
                this.download_queue_start();
                //reset download retry
                this.download_retry = 0;
            }
        }, false);
        xhr.addEventListener("abort", (evt) => {
            delete this.download_queue[index];
            this.download_queue_start();
        }, false);
        xhr.open("GET", url);
        xhr.onload = () => {
            this.download_queue_complete(xhr, filename, id, index);
        };
        xhr.responseType = 'blob';
        xhr.send();
    }

    download_queue_complete(evt, filename, id, index) {
        this.download_retry = 0;
        let blob = new Blob([evt.response], {
            type: evt.response.type
        });
        //ie的下载
        if (window.navigator.msSaveOrOpenBlob) {
            navigator.msSaveBlob(blob, filename);
        } else {
            //非ie的下载
            let link = document.createElement('a');
            link.href = window.URL.createObjectURL(blob);
            link.download = filename;
            link.click();
            window.URL.revokeObjectURL(link.href);
        }
        this.download_queue_processing = false;
        //关闭进度条
        //$('.download_progress_bar_' + index).hide();
        //恢复进度条样式
        $('.btn_download_' + index).removeAttr('disabled');
        $('.btn_download_' + index).html('<i class="fa-fw fad fa-download"></i>');

        delete this.download_queue[index];
        this.download_queue_run();
    }

    download_progress_on(evt, id, filename, index) {
        //$('#download_queue_' + id).html(TL.languageData.download_run + filename + ' (' + this.bytetoconver(evt.loaded, true) + ' / ' + this.bytetoconver(evt.total, true) + ')');
        $('.download_progress_bar_set_' + index).css('width', (evt.loaded / evt.total) * 100 + '%');
        if (evt.loaded == evt.total) {
            $('.download_progress_bar_' + index).fadeOut();
        }
    }

    download_file() {
        this.loading_box_on();
        // $('#btn_download').addClass('disabled');
        // $('#btn_download').html(this.languageData.file_btn_download_status0);
        $.post(this.api_file, {
            action: 'download_check',
            token: this.api_token
        }, (rsp) => {
            if (rsp.status == 1) {
                // location.href = $('#btn_download').attr('x-href');
                // $('#btn_download').html(this.languageData.file_btn_download_status2);
                this.single_download_start($('.single_download_progress_bar').attr('data-href'), $('.single_download_progress_bar').attr('data-filename'));
            } else {
                $('#btn_download').html(this.languageData.file_btn_download_status1);
            }
            // setTimeout(() => {
            //     $('#btn_download').removeClass('disabled');
            //     $('#btn_download').html(this.languageData.file_btn_download);
            // }, 3000);
            this.loading_box_off();
        }, 'json');
    }

    download_file_btn(i) {
        let ukey = this.list_data[i].ukey;
        let title = this.list_data[i].fname;
        let size = this.list_data[i].fsize_formated;
        let type = this.list_data[i].ftype;
        // $('#btn_download_' + ukey).addClass('disabled');
        // $('#btn_download_' + ukey).html('<i class="fas fa-check-circle fa-fw text-green"></i>');
        // if (this.isMobile()) {
        //     window.open('https://tmplinkapp-connect.vx-cdn.com/connect-' + this.api_token + '-' + ukey);
        //     return false;
        // }
        this.download_queue_add('https://tmplinkapp-connect.vx-cdn.com/connect-' + this.api_token + '-' + ukey, title, ukey, size, type);
        this.download_queue_start();
        //this.download_queue_run();
        // setTimeout(() => {
        //     $('#btn_download_' + ukey).removeClass('disabled');
        //     $('#btn_download_' + ukey).html('<i class="fad fa-download"></i>');
        // }, 3000);
        $('.download_progress_bar_' + ukey).show();
        $('.btn_download_' + ukey).attr('disabled', 'true');
        $('.btn_download_' + ukey).html('<i class="fa-fw fas fa-spinner fa-pulse"></i>');
    }

    download_allfile_btn() {
        //在移动设备上无法使用全部下载功能
        let room_key = 'app_room_view' + this.room.mr_id;
        // if (this.isMobile()) {
        //     this.alert(this.languageData.alert_no_support);
        //     return false;
        // }
        this.loading_box_on();
        let search = $('#room_search').val();
        var params = this.get_url_params();
        this.recaptcha_do('mr_addlist', (recaptcha) => {
            let photo = 0;
            if (localStorage.getItem(room_key) == 'photo') {
                photo = 1;
            }
            $.post(this.api_mr, {
                action: 'file_list_page',
                token: this.api_token,
                //captcha: recaptcha,
                page: 'all',
                photo: photo,
                mr_id: params.mrid,
                search: search
            }, (rsp) => {
                if (rsp.status != 0) {
                    this.autoload = true;
                    this.list_data = rsp.data;
                    //在下载全部文件之前，需要先刷新列表
                    this.mr_file_view(rsp.data, 0, params.mrid);
                    //关闭自动载入功能
                    this.room_filelist_autoload_disabled();
                    //启动下载
                    setTimeout(() => {
                        for (let i in rsp.data) {
                            this.download_file_btn(i);
                        }
                    }, 1000);
                    // for (let i in rsp.data) {
                    //     this.download_file_btn(i);
                    // }
                } else {
                    this.autoload = false;
                }
                this.loading_box_off();
            });
        });
    }

    cli_uploader_generator() {
        $('#cli_copy').attr('disabled', true);
        this.recaptcha_do('upload_cli', (recaptcha) => {
            $.post(this.api_url_upload, {
                'token': this.api_token,
                'action': 'upload_request',
                'captcha': recaptcha
            }, (rsp) => {
                if (rsp.status != 0) {
                    let path = $('#cli_upload_path').val();
                    let model = $('#cli_upload_model').val();
                    let utoken = rsp.data;
                    let text = 'curl -k -F "file=@' + path + '" -F "token=' + this.api_token + '" -F "model=' + model + '" -F "utoken=' + utoken + '" -X POST "https://connect.tmp.link/api_v2/cli_uploader2"';
                    let tpl = {
                        utoken: utoken,
                        cmd: text
                    };

                    $('#cliuploader_request_list').prepend(app.tpl('uploadcli_list_tpl', tpl));
                    $('#cli_copy_' + utoken).attr('data-clipboard-text', text);
                    $('#cli_copy').removeAttr('disabled');
                    this.btn_copy_bind();
                }
            });
        });
    }

    storage_buy_modal() {
        if (this.logined === 0) {
            this.alert(this.languageData.status_need_login);
            return false;
        }
        $('#storageModal').modal('show');
    }

    hs_buy_modal() {
        if (this.logined === 0) {
            this.alert(this.languageData.status_need_login);
            return false;
        }
        $('#highspeedModal').modal('show');
    }

    hs_download_file(filename) {
        if (this.logined === 0) {
            this.alert(this.languageData.status_need_login);
            return false;
        }
        $('#btn_highdownload').addClass('disabled');
        $('#btn_highdownload').html(this.languageData.file_btn_download_status0);
        $.post(this.api_file, {
            action: 'highspeed_check',
            token: this.api_token
        }, (rsp) => {
            if (rsp.status == 0) {
                $('#highspeedModal').modal('show');
                $('#btn_highdownload').removeClass('disabled');
                $('#btn_highdownload').html(this.languageData.file_btn_highdownload);
            } else {
                $.post(this.api_file, {
                    action: 'download_check',
                    token: this.api_token
                }, (rsp) => {
                    if (rsp.status == 1) {
                        // location.href = $('#btn_download').attr('x-href');
                        // $('#btn_highdownload').html(this.languageData.file_btn_download_status2);
                        this.single_download_start($('.single_download_progress_bar').attr('data-href'), $('.single_download_progress_bar').attr('data-filename'));
                    } else {
                        $('#btn_highdownload').html(this.languageData.file_btn_download_status1);
                    }
                    setTimeout(() => {
                        $('#btn_highdownload').removeClass('disabled');
                        $('#btn_highdownload').html(this.languageData.file_btn_highdownload);
                    }, 3000);
                }, 'json');
            }
        }, 'json');
    }

    hs_download_buy() {
        if (this.logined === 0) {
            this.alert(this.this.languageData.status_need_login);
            return false;
        }
        var price = $('#highspeed_opt').val();
        var time = $('#highspeed_time').val();
        var code = 'HS';
        var total_price = price * time;

        var link = "https://pay.vezii.com/id4/pay_v2?price=" + total_price + "&token=" + this.api_token + "&prepare_code=" + code + "&prepare_type=addon&prepare_times=" + time;
        window.open(link, '_blank');
    }

    storage_buy() {
        if (this.logined === 0) {
            this.alert(this.this.languageData.status_need_login);
            return false;
        }
        var price = 0;
        var code = $('#storage_code').val();
        var time = $('#storage_time').val();
        switch (code) {
            case '256GB':
                price = 6 * time;
                break;
            case '1TB':
                price = 15 * time;
                break;
            case '3TB':
                price = 38 * time;
                break;
            case '10TB':
                price = 98 * time;
                break;
        }
        var link = "https://pay.vezii.com/id4/pay_v2?price=" + price + "&token=" + this.api_token + "&prepare_code=" + code + "&prepare_type=addon&prepare_times=" + time;
        window.open(link, '_blank');
    }

    orders_list() {
        this.recaptcha_do('order_list', (recaptcha) => {
            $.post(this.api_user, {
                action: 'order_list',
                token: this.api_token,
                //captcha: recaptcha
            }, (rsp) => {
                if (rsp.data.service == 0) {
                    $('#orders_addon_contents').html('<div class="text-center"><i class="fa-fw fad fa-folder-open fa-4x"></i></div>');
                } else {
                    $('#orders_addon_contents').html('<div class="row" id="orders_services_contents"></div>');

                    var service_list = rsp.data.service;
                    var r = this.service_code(service_list);
                    $('#order_list').html(app.tpl('order_list_tpl', r));
                }
                $('#orders_loader').fadeOut();
                $('#orders_loaded').fadeIn();
            }, 'json');
        });
    }

    service_code(data) {
        var r = {};
        for (let i in data) {
            r[i] = {};
            r[i].name = '';
            r[i].des = '';
            r[i].icon = '';
            r[i].etime = data[i].etime;
            switch (data[i].code) {
                case 'hs':
                    r[i].name = this.languageData.service_code_hs;
                    r[i].des = this.languageData.service_code_hs_des;
                    r[i].icon = 'fas fa-rabbit-fast';
                    break;
                case 'storage':
                    r[i].name = this.languageData.service_code_storage + ' (' + this.bytetoconver(data[i].val, true) + ')';
                    r[i].des = this.languageData.service_code_storage_des;
                    r[i].icon = 'fad fa-box-heart';
                    break;
            }
        }
        return r;
    }

    mr_file_addlist() {
        var params = this.get_url_params();
        $('#mrfile_add_list').html('<i class="fa-4x fa-fw fad fa-spinner-third fa-spin mx-auto"></i>');
        this.recaptcha_do('mr_list', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'file_addlist',
                token: this.api_token,
                //captcha: recaptcha,
                mr_id: params.mrid
            }, (rsp) => {
                if (rsp.status == 0) {
                    $('#mrfile_add_list').html('<div class="mx-auto"><i class="fa-fw fad fa-folder-open fa-4x"></i></div>');
                } else {
                    $('#mrfile_add_list').html(app.tpl('mrfile_add_list_tpl', rsp.data));
                }
            });
        });
    }

    mr_file_add(ukey) {
        var params = this.get_url_params();
        $('#btn-mraddlist-' + ukey).fadeOut(300);
        this.recaptcha_do('mr_add', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'file_add',
                token: this.api_token,
                //captcha: recaptcha,
                mr_id: params.mrid,
                ukey: ukey
            }, (rsp) => {
                $('#mraddlist-' + ukey).fadeOut(500);
            });
        });
    }

    mr_file_list(page) {
        $('.no_files').fadeOut();
        $('.no_photos').fadeOut();
        let room_key = 'app_room_view' + this.room.mr_id;
        if (page == 0) {
            this.page_number = 0;
            $('#room_filelist').html('');
            this.list_data = [];
        } else {
            this.page_number++;
        }
        //if search
        let search = $('#room_search').val();

        $('#room_filelist_box').show();
        $('#mr_filelist_refresh_icon').addClass('fa-spin');
        $('#mr_filelist_refresh_icon').attr('disabled', true);
        this.loading_box_on();
        var params = this.get_url_params();
        this.recaptcha_do('mr_addlist', (recaptcha) => {
            let photo = 0;
            if (localStorage.getItem('room_key') == 'photo') {
                photo = 1;
            }
            $.post(this.api_mr, {
                action: 'file_list_page',
                token: this.api_token,
                //captcha: recaptcha,
                page: this.page_number,
                photo: photo,
                mr_id: params.mrid,
                sort_by: this.sort_by,
                sort_type: this.sort_type,
                search: search
            }, (rsp) => {
                $('.data_loading').hide();
                $('#mr_filelist_refresh_icon').removeClass('fa-spin');
                $('#mr_filelist_refresh_icon').removeAttr('disabled');
                this.mr_file_view(rsp.data, page, params.mrid);
                if (rsp.status != 0) {
                    this.autoload = true;
                    for (let i in rsp.data) {
                        this.list_data[rsp.data[i].ukey] = rsp.data[i];
                    }
                } else {
                    this.autoload = false;
                }

                //cancel
                if (rsp.status == 0 || rsp.data.length < 50) {
                    this.room_filelist_autoload_disabled();
                }
                this.loading_box_off();
            });
        });
    }

    room_performance_init(room_id) {
        let room_key = 'app_room_view' + room_id;
        let storage_room_display = localStorage.getItem(room_key);
        let room_display = storage_room_display === null ? this.room.display : storage_room_display;
        localStorage.setItem(room_key, room_display);
        $("#pf_display option[value='" + this.room.display + "']").attr("selected", "selected");
    }

    room_performance_open() {
        $('#btn_pf_confirm').removeAttr('disabled');
        $('#performanceModal').modal('show');
    }

    room_performance_post() {
        let pf_display = $('#pf_display').val();
        let mrid = this.room.mr_id;
        $('#btn_pf_confirm').attr('disabled', 'disabled');
        $.post(this.api_mr, {
            action: 'pf_set',
            token: this.api_token,
            pf_display: pf_display,
            mr_id: mrid
        }, () => {
            $('#performanceModal').modal('hide');
        });
    }

    room_filelist_model(type) {
        let room_key = 'app_room_view' + this.room.mr_id;
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
        this.mr_file_list(0);
    }

    room_btn_active_reset() {
        $('#room_btn_file_list').removeClass('bg-dark');
        $('#room_btn_file_grid').removeClass('bg-dark');
        $('#room_btn_file_photo').removeClass('bg-dark');
    }

    room_filelist_autoload_enabled() {
        this.autoload = true;
        $(window).on("scroll", (event) => {
            if ($(event.currentTarget).scrollTop() + $(window).height() + 100 >= $(document).height() && $(event.currentTarget).scrollTop() > 100) {
                if (this.autoload == true) {
                    this.autoload = false;
                    this.mr_file_list(1);
                }
            }
        });
    }

    room_filelist_autoload_disabled() {
        $(window).off("scroll");
    }

    mr_file_by_list(data, page) {
        this.room_btn_active_reset();
        $('#room_btn_file_list').addClass('bg-dark');
        if (page == 0) {
            $('#room_filelist').html('');
            if (this.subroom_data.length != 0) {
                $('#room_filelist').append(app.tpl('meetroom_list_tpl', this.subroom_data));
            }
            if (data === false && this.subroom_data == 0) {
                $('.no_files').fadeIn();
            }
        }
        if (data.length != 0) {
            $('#room_filelist').append(app.tpl('room_filelist_list_tpl', data));
        }
        this.btn_copy_bind();
        app.linkRebind();
    }

    mr_file_by_photo(data, page) {
        this.room_btn_active_reset();
        $('#room_btn_file_photo').addClass('bg-dark');
        if (page == 0) {
            $('#room_filelist').html('');
            if (this.subroom_data.length != 0) {
                $('#room_filelist').append(app.tpl('meetroom_list_tpl', this.subroom_data));
            }
            if (data === false && this.subroom_data == 0) {
                $('.no_photos').fadeIn();
            }
        }
        if (data.length != 0) {
            $('#room_filelist').append(app.tpl('room_filelist_photo_tpl', data));
        }
        this.btn_copy_bind();
        app.linkRebind();
        this.lazyLoadInstance.update();
    }

    mr_file_del(ukey) {
        var params = this.get_url_params();
        $('#file_unit_' + ukey).hide(300);
        this.recaptcha_do('mr_del', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'file_del',
                token: this.api_token,
                //captcha: recaptcha,
                mr_id: params.mrid,
                ukey: ukey
            }, () => {
                //this.mr_file_list();
            });
        });
    }

    mr_user_add() {
        var params = this.get_url_params();
        var email = $('#modal_add_user').val();
        if (email == '') {
            return false;
        }
        $('#modal_add_user_btn').fadeOut(300);
        this.recaptcha_do('mr_add', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'user_add',
                token: this.api_token,
                //captcha: recaptcha,
                mr_id: params.mrid,
                email: email
            }, (rsp) => {
                $('#notice_add_user').addClass('alert-danger');
                $('#notice_add_user').html(this.languageData.form_btn_processed);
                this.mr_user_list();
                setTimeout(() => {
                    $('#notice_add_user').removeClass('alert-danger');
                    $('#notice_add_user').html(this.languageData.model_add_user_notice);
                    $('#modal_add_user_btn').fadeIn(300);
                }, 2000);
            });
        });
    }

    mr_user_list() {
        $('#room_userlist_box').show();
        $('#mr_userlist_refresh_icon').html('<i class="fa-fw fad fa-spinner-third fa-spin"></i>');
        $('#mr_userlist_refresh_icon').attr('disabled', true);
        var params = this.get_url_params();
        this.recaptcha_do('mr_addlist', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'user_list',
                token: this.api_token,
                //captcha: recaptcha,
                mr_id: params.mrid
            }, (rsp) => {
                $('#mr_userlist_refresh_icon').html('<i class="fa-fw fas fa-sync-alt"></i>');
                $('#mr_userlist_refresh_icon').removeAttr('disabled');
                if (rsp.status == 0) {
                    $('#room_userlist').html('<i class="fa-4x fad fa-user-alt-slash mx-auto"></i>');
                } else {
                    $('#room_userlist').html(app.tpl('room_userlist_tpl', rsp.data));
                }
            });
        });
    }

    mr_user_del(id) {
        var params = this.get_url_params();
        $('#btn-mrdel-user-' + id).fadeOut(300);
        this.recaptcha_do('mr_add', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'user_del',
                token: this.api_token,
                //captcha: recaptcha,
                mr_id: params.mrid,
                delete: id
            }, (rsp) => {
                $('#mr-user-' + id).fadeOut(500);
            });
        });
    }

    mr_add() {
        var name = $('#modal_meetingroom_create_name').val();
        var model = $('#modal_meetingroom_create_type').val();
        var mr_id = $('#mr_id').val();
        var parent = $('#mr_parent_id').val();
        var top = $('#mr_top_id').val();
        if (model == '' && name == '') {
            $('#notice_meetingroom_create').html(this.languageData.notice_meetingroom_status_mrcreat_fail);
            return false;
        }
        if (parent > 0) {
            model = 0;
        }
        $('#modal_meetingroom_create_btn').attr('disabled', true);
        $('#notice_meetingroom_create').html(this.languageData.notice_meetingroom_status_proccessing);
        this.recaptcha_do('mr_add', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'create',
                token: this.api_token,
                //captcha: recaptcha,
                name: name,
                mr_id: mr_id,
                parent: parent,
                top: top,
                model: model
            }, (rsp) => {
                if (rsp.status == 1) {
                    $('#notice_meetingroom_create').html(this.languageData.notice_meetingroom_status_mrcreated);
                    if (mr_id == 0) {
                        this.mr_list();
                    } else {
                        this.room_list();
                    }
                    $('#mrCreaterModal').modal('hide');
                } else {
                    $('#notice_meetingroom_create').html(this.languageData.notice_meetingroom_status_mrcreat_fail);
                }
                setTimeout(() => {
                    $('#modal_meetingroom_create_btn').removeAttr('disabled');
                }, 2000);
            });
        });
    }

    mr_del(mrid) {
        $('#meetingroom_id_' + mrid).fadeOut();
        this.recaptcha_do('mr_del', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'delete',
                token: this.api_token,
                //captcha: recaptcha,
                mr_id: mrid
            });
        });
    }

    mr_exit(mrid) {
        $('#meetingroom_id_' + mrid).hide();
        this.recaptcha_do('mr_del', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'exit',
                token: this.api_token,
                //captcha: recaptcha,
                mr_id: mrid
            });
        });
    }

    mr_newname(mrid) {
        var newname = prompt(this.languageData.modal_meetingroom_newname, "none");
        this.recaptcha_do('mr_newname', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'rename',
                token: this.api_token,
                //captcha: recaptcha,
                name: newname,
                mr_id: mrid
            }, (rsp) => {
                this.room_list();
            });
        });
    }

    mr_list() {
        if (localStorage.getItem('app_login') != 1) {
            app.open('/login');
            return;
        }
        $('#mr_list_refresh_icon').html('<i class="fa-fw fad fa-spinner-third fa-spin"></i>');
        $('#mr_list_refresh_icon').attr('disabled', true);
        this.loading_box_on();
        this.recaptcha_do('mr_add', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'list',
                token: this.api_token,
                //captcha: recaptcha
            }, (rsp) => {
                this.loading_box_off();
                if (rsp.status == 0) {
                    $('#meetroom_list').html('<div class="mx-auto"><i class="fa-fw fad fa-folder-open fa-4x"></i></div>');
                    $('#mr_list_refresh_icon').html('<i class="fa-fw fas fa-sync-alt"></i>');
                    $('#mr_list_refresh_icon').removeAttr('disabled');
                    return false;
                } else {
                    $('#meetroom_list').html(app.tpl('meetroom_list_tpl', rsp.data));
                    this.btn_copy_bind();
                }
                $('#mr_list_refresh_icon').html('<i class="fa-fw fas fa-sync-alt"></i>');
                $('#mr_list_refresh_icon').removeAttr('disabled');
                app.linkRebind();
            });
        });
    }

    mr_file_view(data, page, room_id) {
        let room_key = 'app_room_view' + room_id;
        switch (localStorage.getItem(room_key)) {
            case 'photo':
                this.mr_file_by_photo(data, page);
                break;
            case 'list':
                this.mr_file_by_list(data, page);
                break;
            default:
                this.mr_file_by_list(data, page);
        }
    }


    room_list() {
        var params = this.get_url_params();
        $('#room_userlist').hide();
        $('.permission-room-file').hide();
        $('.permission-room-user').hide();
        $('.data_loading').show();
        //this.loading_box_on();
        //获取基本信息
        this.recaptcha_do('room_list', (recaptcha) => {
            $.post(this.api_mr, {
                action: 'details',
                //captcha: recaptcha,
                token: this.api_token,
                mr_id: params.mrid
            }, (rsp) => {
                this.room_data = rsp.data;
                $('.data_loading').hide();
                this.loading_box_off();
                if (rsp.status === 0) {
                    //会议室不存在了
                    this.room.parent = 0;
                    this.room.top = 0;
                    this.room.ownner = 0;
                    this.room.mr_id = 0;
                    $('#file_messenger_icon').html('<i class="fas fa-folder-times  fa-4x"></i>');
                    $('#file_messenger_msg').html(this.languageData.room_status_fail);
                    $('#file_messenger').show();
                    gtag('config', 'UA-96864664-3', {
                        'page_title': 'F-Unavailable',
                    });
                    return false;
                } else {
                    gtag('config', 'UA-96864664-3', {
                        'page_title': 'F-' + rsp.data.name,
                    });
                    this.room.parent = rsp.data.parent;
                    this.room.top = rsp.data.top;
                    this.room.owner = rsp.data.owner;
                    this.room.mr_id = rsp.data.mr_id;
                    this.room.display = rsp.data.display;
                    this.room_performance_init(this.room.mr_id);
                    $('#mr_copy').attr('data-clipboard-text', 'http://tmp.link/room/' + rsp.data.mr_id);
                    $('.room_title').html(rsp.data.name);
                    $('#room_filelist').show();
                    if (rsp.data.sub_rooms !== 0) {
                        this.subroom_data = rsp.data.sub_rooms;
                    } else {
                        this.subroom_data = 0;
                    }

                    if (this.room.owner === 0) {
                        $('.not_owner').hide();
                    }

                    this.btn_copy_bind();
                    this.mr_file_list(0);

                    //是否需要设置上级目录返回按钮
                    $('#room_back_btn').html(app.tpl('room_back_btn_tpl', {}));
                    $('#room_loading').hide();
                    $('#room_loaded').fadeIn();
                    app.linkRebind();
                }
            });
        });
    }

    login() {
        var email = $('#email').val();
        var password = $('#password').val();
        $('#submit').attr('disabled', true);
        $('#msg_notice').fadeIn();
        $('#submit').html(this.languageData.form_btn_processing);
        $('#msg_notice').html(this.languageData.form_btn_processing);
        this.recaptcha_do('init', (recaptcha) => {
            if (email !== '' && password !== '') {
                $.post(this.api_user, {
                    action: 'login',
                    token: this.api_token,
                    captcha: recaptcha,
                    email: email,
                    password: password
                }, (rsp) => {
                    if (rsp.status == 1) {
                        $('#msg_notice').html(this.languageData.login_ok);
                        this.logined = 1;
                        this.get_details(() => {
                            localStorage.setItem('app_login', 1);
                            window.history.back();
                            //app.open('/workspace');
                        });
                    } else {
                        $('#msg_notice').html(this.languageData.login_fail);
                        $('#submit').html(this.languageData.form_btn_login);
                        $('#submit').removeAttr('disabled');
                    }
                });
            }
        });
    }

    language(lang) {
        if (this.logined === 1) {
            $.post(this.api_user, {
                action: 'language',
                token: this.api_token,
                lang: lang
            });
        }
        var span_lang = 'English';
        if (lang === 'en') {
            span_lang = 'English';
        }

        if (lang === 'cn') {
            span_lang = '简体';
        }

        if (lang === 'hk') {
            span_lang = '繁体';
        }

        if (lang === 'jp') {
            span_lang = '日本語';
        }

        if (lang === 'ru') {
            span_lang = 'русский';
        }

        if (lang === 'kr') {
            span_lang = '한국어';
        }

        if (lang === 'my') {
            span_lang = 'Melayu';
        }
        $('.selected_lang').html(span_lang);
        app.languageSet(lang);
    }

    logout() {
        localStorage.setItem('app_login', 0);
        this.uid = 0;
        this.logined = 0;
        this.storage_used = 0;
        this.storage = 0;
        app.open('/');
        $.post(this.api_user, {
            action: 'logout',
            token: this.api_token
        });
    }

    register() {
        var email = $('#email').val();
        var password = $('#password').val();
        var rpassword = $('#rpassword').val();
        var code = $('#checkcode').val();
        $('#msg_notice').fadeIn();
        $('#msg_notice').html(this.languageData.form_btn_processing);
        $('#submit').html(this.languageData.form_btn_login);
        $('#submit').attr('disabled', true);
        this.recaptcha_do('init', (recaptcha) => {
            $.post(this.api_user, {
                action: 'register',
                token: this.api_token,
                email: email,
                password: password,
                captcha: recaptcha,
                rpassword: rpassword,
                code: code
            }, (rsp) => {
                if (rsp.status === 1) {
                    $('#msg_notice').html(this.languageData.reg_finish);
                    $('#submit').html(this.languageData.reg_finish);
                    this.get_details(() => {
                        gtag('event', 'conversion', {
                            'send_to': 'AW-977119233/7Pa-CNH4qbkBEIHQ9tED'
                        });
                        setTimeout(() => {
                            app.open('/workspace');
                        }, 3000);
                    });
                } else {
                    $('#msg_notice').html(rsp.data);
                    $('#submit').html(this.languageData.form_btn_login);
                    $('#submit').removeAttr('disabled');
                }
            });
        });
    }

    cc_send() {
        var email = $('#email').val();
        $('#msg_notice').fadeIn();
        $('#msg_notice').html(this.languageData.form_btn_processing);
        $('#button-reg-checkcode').html(this.languageData.form_btn_processing);
        $('#button-reg-checkcode').attr('disabled', true);
        this.recaptcha_do('checkcode', (recaptcha) => {
            if (email !== '') {
                $.post(this.api_user, {
                    action: 'checkcode_send',
                    token: this.api_token,
                    captcha: recaptcha,
                    lang: app.languageGet(),
                    email: email
                }, (rsp) => {
                    if (rsp.status == 1) {
                        $('#msg_notice').html(this.languageData.form_checkcode_msg_sended);
                        $('#button-reg-checkcode').html(this.languageData.form_checkcode_sended);
                    } else {
                        $('#msg_notice').html(this.error_text(rsp.status));
                        $('#button-reg-checkcode').html(this.languageData.form_getcode);
                        $('#button-reg-checkcode').removeAttr('disabled');
                    }
                });
            }
        });
    }

    error_text(code) {
        let msg = this.languageData.status_error_0;
        switch (code) {
            case 9:
                msg = this.languageData.status_error_9;
                break;
            case 11:
                msg = this.languageData.status_error_11;
                break;
            case 10:
                msg = this.languageData.status_error_10;
                break;
        }
        return msg;
    }

    upload_queue_clean() {
        $('.upload_file_ok').remove();
        if (this.upload_queue_file.length > 0) {
            for (let x in this.upload_queue_file) {
                $('#uq_' + id).remove();
            }
            this.upload_queue_file = [];
        }
    }

    upload_cli() {
        if (this.logined === 1) {
            $('#uploadCliModal').modal('show');
            $('#upload_cli_token').html(this.api_token);
        } else {
            this.alert(this.languageData.status_need_login);
            app.open('/login');
        }
    }

    upload_open(mr_id) {
        if (!this.logined) {
            this.alert(this.languageData.status_need_login);
            return false;
        }

        this.storage_status_update();
        if (mr_id == 0) {
            $('#dirsToUpload').hide();
            $('#dirsToUpload_label').hide();
        }

        this.upload_model_selected(Number(this.upload_model_selected_val));

        $('#upload_mr_id').val(mr_id);
        $('#uploadModal').modal('show');
    }

    upload_start() {
        if (this.upload_processing == 1) {
            return false;
        }
        if (this.upload_queue_file.length > 0) {
            let f = this.upload_queue_file.shift();
            if (typeof f === 'object') {
                this.upload_processing = 1;
                this.upload_core(f, f.is_dir);
            }
        }
    }

    upload_queue_remove(id) {
        // delete this.upload_queue_file[id];
        // this.upload_queue_file.length--;
        $('#uq_' + id).hide();
    }

    upload_model_get() {
        return $("#upload_model").val();
    }

    upload_mrid_get() {
        return $("#upload_mr_id").val();
    }

    upload_core(file_res, is_dir) {
        $('#nav_upload_btn').html('<i class="fa-fw fad fa-spinner-third fa-spin"></i>');
        let file = file_res.file;
        let id = file_res.id;
        let model = this.upload_model_get();
        if (file.size > this.single_file_size) {
            this.alert(this.languageData.upload_limit_size);
            $('#uq_' + id).fadeOut();
            return false;
        }
        if (this.logined === false) {
            $('#notice_upload').html(this.languageData.upload_model99_needs_login);
            $('#uq_' + id).fadeOut();
            return false;
        }
        if (this.storage == 0) {
            $('#notice_upload').html(this.languageData.upload_buy_storage);
            $('#uq_' + id).fadeOut();
            return false;
        }
        if (file.size > (this.storage - this.storage_used)) {
            $('#notice_upload').html(this.languageData.upload_fail_storage);
            $('#uq_' + id).fadeOut();
            return false;
        }
        $('#uq_delete_' + id).hide();
        $('#notice_upload').html(this.languageData.upload_upload_prepare);
        this.upload_prepare(file, id, (f, sha1, id) => {
            //如果sha1不等于0，则调用另外的接口直接发送文件名信息。
            let filename = is_dir ? file.webkitRelativePath : file.name;
            if (sha1 !== 0) {
                $.post(this.api_file, {
                    'sha1': sha1,
                    'filename': filename,
                    'model': this.upload_model_get(),
                    'mr_id': this.upload_mrid_get(),
                    'action': 'prepare_v4',
                    'token': this.api_token
                }, (rsp) => {
                    if (rsp.status === 1) {
                        this.upload_final(rsp, file, id);
                        this.upload_processing = 0;
                        this.upload_start();
                    } else {
                        this.upload_worker(f, id, filename);
                    }
                }, 'json');
            } else {
                this.upload_worker(f, id);
            }
        });
    }



    upload_prepare(file, id, callback) {
        //不支持FileReader，直接下一步。
        if (!window.FileReader) {
            callback(file, 0, id);
            return false;
        }
        //支持FileReader，计算sha1再进行下一步
        var reader = new FileReader();
        reader.onload = (event) => {
            var file_sha1 = sha1(event.target.result);
            callback(file, file_sha1, id);
        };
        reader.readAsArrayBuffer(file.slice(0, (1024 * 1024 * 32)));
    }

    upload_worker(file, id, filename) {
        this.recaptcha_do('upload_web', (recaptcha) => {
            $.post(this.api_url_upload, {
                'token': this.api_token,
                'action': 'upload_request_select',
                'captcha': recaptcha
            }, (rsp) => {
                var fd = new FormData();
                fd.append("file", file);
                fd.append("filename", filename);
                fd.append("utoken", rsp.data.utoken);
                fd.append("model", this.upload_model_get());
                fd.append("mr_id", this.upload_mrid_get());
                fd.append("token", this.api_token);
                this.upload_s2_status[id] = 0;
                var xhr = new XMLHttpRequest();
                xhr.upload.addEventListener("progress", (evt) => {
                    this.upload_progress(evt, id)
                }, false);
                xhr.addEventListener("load", (evt) => {
                    this.upload_complete(evt, file, id)
                }, false);
                xhr.addEventListener("error", (evt) => {
                    //add retry
                    if (this.download_retry < this.download_retry_max) {
                        this.download_retry++;
                        setTimeout(()=>{
                            this.upload_worker(file, id, filename);
                        },1000);
                    } else {
                        this.download_retry = 0;
                        this.upload_failed(evt, id);
                    }
                }, false);
                xhr.addEventListener("abort", (evt) => {
                    this.upload_canceled(evt, id)
                }, false);
                xhr.open("POST", rsp.data.uploader);
                xhr.send(fd);
            });
        });
    }

    upload_progressbar_counter_total = []
    upload_progressbar_counter_loaded = []
    upload_progressbar_counter_count = []
    upload_progressbar_counter = []

    upload_progressbar_draw(id) {
        if (this.upload_progressbar_counter_count[id] == 0) {
            return false;
        }
        let speed = this.upload_progressbar_counter_count[id];
        let left_time = this.formatTime(Math.ceil((this.upload_progressbar_counter_total[id] - this.upload_progressbar_counter_loaded[id]) / speed));
        let msg = this.bytetoconver(this.upload_progressbar_counter_loaded[id], true) + ' / ' + this.bytetoconver(this.upload_progressbar_counter_total[id], true);
        let uqmid = "#uqm_" + id;
        let uqpid = "#uqp_" + id;
        msg += ' | ' + this.bytetoconver(speed, true) + '/s | ' + left_time;
        $(uqmid).html(msg);
        var percentComplete = Math.round(this.upload_progressbar_counter_loaded[id] * 100 / this.upload_progressbar_counter_total[id]);
        $(uqpid).css('width', percentComplete + '%');
        this.upload_s2_status[id] = this.upload_progressbar_counter_loaded[id];
        this.upload_progressbar_counter_count[id] = 0;
    }

    upload_selected() {
        let file = document.getElementById('fileToUpload').files;
        let f = null;
        if (file.length > 0) {
            for (let x in file) {
                f = file[x];
                if (typeof f !== 'object') {
                    continue;
                }
                if (f.size !== 0) {
                    this.upload_queue_add({
                        file: f,
                        is_dir: false
                    });
                }
            }
        }
    }

    upload_dir_selected() {
        let file = document.getElementById('dirsToUpload').files;
        let f = null;
        if (file.length > 0) {
            for (let x in file) {
                f = file[x];
                if (typeof f !== 'object') {
                    continue;
                }
                if (f.size !== 0) {
                    this.upload_queue_add({
                        file: f,
                        is_dir: true
                    });
                }
            }
        }
    }


    upload_drop(e) {
        e.preventDefault();
        var fileList = e.dataTransfer.files;
        //files
        if (fileList.length == 0) {
            return false;
        }
        for (let x in fileList) {
            if (typeof fileList[x] === 'object') {
                setTimeout(() => {
                    this.upload_queue_add({
                        file: fileList[x],
                        is_dir: false
                    });
                }, 500);
            }
        }

        if (this.upload_processing == 0) {
            this.upload_start();
        }
    }

    upload_queue_add(f) {
        setTimeout(() => {
            f.id = this.upload_queue_id;
            this.upload_queue_file.push(f);
            let file = f.file;
            $('#uploaded_file_box').append(app.tpl('upload_list_wait_tpl', {
                name: file.name,
                size: this.bytetoconver(file.size, true),
                id: this.upload_queue_id
            }));
            $('#uploaded_file_box').show();
            this.upload_queue_id++;
            //自动启动上传
            this.upload_start();
        }, 500, f);
    }

    upload_progress(evt, id) {
        if (evt.lengthComputable) {
            if (evt.total === evt.loaded) {
                $('#notice_upload').html(this.languageData.upload_sync);
                $('#uqp_' + id).css('width', '100%');
                $('#uqp_' + id).addClass('progress-bar-striped');
                $('#uqp_' + id).addClass('progress-bar-animated');
                clearInterval(this.upload_progressbar_counter[id]);
                this.upload_progressbar_counter[id] = null;
                //执行下一个上传
                // delete this.upload_queue_file[id];
                // this.upload_queue_file.length--;
                this.upload_processing = 0;
                this.upload_start();
            } else {
                //
                this.upload_progressbar_counter_count[id] += evt.loaded - this.upload_s2_status[id];
                this.upload_s2_status[id] = evt.loaded;
                //
                this.upload_progressbar_counter_total[id] = evt.total;
                this.upload_progressbar_counter_loaded[id] = evt.loaded;
                //检查进度条是否运行
                if (this.upload_progressbar_counter[id] === undefined) {
                    this.upload_progressbar_counter[id] = setInterval(() => {
                        this.upload_progressbar_draw(id);
                    }, 1000);
                }
            }
        }
    }

    upload_complete(evt, file, id) {
        this.download_retry = 0;
        clearInterval(this.upload_progressbar_counter[id]);
        this.upload_progressbar_counter[id] = null;
        var data = JSON.parse(evt.target.responseText);
        this.upload_final(data, file, id);
    }

    upload_failed(evt, id) {
        clearInterval(this.upload_progressbar_counter[id]);
        this.upload_progressbar_counter[id] = null;
        this.alert(this.languageData.upload_fail);
        $('#uq_' + id).fadeOut();
        this.upload_processing = 0;
        this.upload_start();
    }

    upload_canceled(evt, id) {
        clearInterval(this.upload_progressbar_counter[id]);
        this.upload_progressbar_counter[id] = null;
        this.alert(this.languageData.upload_cancel);
        $('#uq_' + id).fadeOut();
        this.upload_processing = 0;
        this.upload_start();
    }

    upload_final(rsp, file, id) {
        $('#uq_' + id).fadeOut();
        $('#nav_upload_btn').html(this.languageData.nav_upload);
        if (rsp.status === 1) {
            // $('#uploaded_file_box').append(app.tpl('upload_list_ok_tpl', {
            //     name: file.name,
            //     size: this.bytetoconver(file.size, true),
            //     ukey: rsp.data.ukey
            // }));
            this.btn_copy_bind();
        } else {
            alert(this.languageData.upload_fail);
        }
        if (this.upload_mrid_get() != 0 && this.upload_queue_file.length == 0) {
            this.room_list();
        }
        if (this.upload_mrid_get() == 0 && this.upload_queue_file.length == 0) {
            this.workspace_filelist();
        }
        $('#notice_upload').html(this.languageData.upload_ok);
        // this.upload_processing = 0;
        // this.upload_start();
    }

    alert(content) {
        $("#alert-modal-content").html(content);
        $("#alertModal").modal('show');
    }

    report() {
        var ukey = $('#report_ukey').html();
        var reason = $('#report_model').val();
        $('#reportbtn').attr('disabled', true);
        $('#reportbtn').html(this.languageData.form_btn_processed);
        $.post(this.api_file, {
            'action': 'report',
            'token': this.api_token,
            'reason': reason,
            'ukey': ukey
        }, (rsp) => {
            $('#reportbtn').html(this.languageData.form_btn_processed);
        }, 'json');
    }

    find_file() {
        var ukey = $('#ukey').val();
        if (ukey !== '') {
            window.open('http://tmp.link/f/' + ukey);
        }
    }

    get_url_params() {
        var vars = [],
            hash;
        var hashes = window.location.href.slice(window.location.href.indexOf('?') + 1).split('&');
        for (var i = 0; i < hashes.length; i++) {
            hash = hashes[i].split('=');
            vars.push(hash[0]);
            vars[hash[0]] = hash[1];
        }
        return vars;
    }

    storage_status_update() {
        let data = {};
        data.storage_text = this.bytetoconver(this.storage, true);
        data.storage_used_text = this.bytetoconver(this.storage_used, true);
        data.percent = (this.storage_used / this.storage) * 100;
        $('#upload_storage_status').html(this.languageData.model_title_buy_storage + ': ' + data.storage_used_text + ' | ' + data.storage_text);
        // $('#upload_storage_status').html(app.tpl('upload_storage_status_tpl', data));
    }

    bytetoconver(val, label) {
        if (val == 0)
            return '0';
        var s = ['B', 'KB', 'MB', 'GB', 'TB', 'PB'];
        var e = Math.floor(Math.log(val) / Math.log(1024));
        var value = ((val / Math.pow(1024, Math.floor(e))).toFixed(2));
        e = (e < 0) ? (-e) : e;
        if (label)
            value += ' ' + s[e];
        return value;
    }

    btn_copy_bind() {
        var clipboard = new Clipboard('.btn_copy');
        clipboard.on('success', (e) => {
            let tmp = $(e.trigger).html();
            $(e.trigger).html('<i class="text-green fas fa-check-circle fa-fw"></i>');
            setTimeout(() => {
                $(e.trigger).html(tmp);
            }, 3000);
        });
    }

    api_init() {
        $.post(this.api_url + '/init', (data) => {
            this.api_file = data + '/file'
            this.api_user = data + '/user'
            this.api_mr = data + '/meetingroom'
        }, 'text');
        $.post(this.api_url + '/init_uploader', (data) => {
            this.api_url_upload = data + '/file'
        }, 'text');
    }

    fileicon(type) {
        var r = 'fad fa-file';
        switch (type) {
            case 'pdf':
                r = 'fad fa-file-pdf';
                break;

            case 'zip':
                r = 'fad fa-file-archive';
                break;
            case 'rar':
                r = 'fad fa-file-archive';
                break;
            case '7z':
                r = 'fad fa-file-archive';
                break;
            case 'gz':
                r = 'fad fa-file-archive';
                break;
            case 'tar':
                r = 'fad fa-file-archive';
                break;

            case 'doc':
                r = 'fad fa-file-word';
                break;
            case 'wps':
                r = 'fad fa-file-word';
                break;
            case 'docx':
                r = 'fad fa-file-word';
                break;

            case 'c':
                r = 'fad fa-file-code';
                break;
            case 'go':
                r = 'fad fa-file-code';
                break;
            case 'cpp':
                r = 'fad fa-file-code';
                break;
            case 'php':
                r = 'fad fa-file-code';
                break;
            case 'java':
                r = 'fad fa-file-code';
                break;
            case 'js':
                r = 'fad fa-file-code';
                break;
            case 'vb':
                r = 'fad fa-file-code';
                break;
            case 'py':
                r = 'fad fa-file-code';
                break;
            case 'css':
                r = 'fad fa-file-code';
                break;
            case 'html':
                r = 'fad fa-file-code';
                break;
            case 'tar':
                r = 'fad fa-file-code';
                break;
            case 'asm':
                r = 'fad fa-file-code';
                break;

            case 'ogg':
                r = 'fad fa-file-music';
                break;
            case 'm4a':
                r = 'fad fa-file-music';
                break;
            case 'mp3':
                r = 'fad fa-file-music';
                break;
            case 'wav':
                r = 'fad fa-file-music';
                break;
            case 'weba':
                r = 'fad fa-file-music';
                break;

            case 'mp4':
                r = 'fad fa-file-video';
                break;
            case 'rm':
                r = 'fad fa-file-video';
                break;
            case 'rmvb':
                r = 'fad fa-file-video';
                break;
            case 'avi':
                r = 'fad fa-file-video';
                break;
            case 'mkv':
                r = 'fad fa-file-video';
                break;
            case 'webm':
                r = 'fad fa-file-video';
                break;
            case 'wmv':
                r = 'fad fa-file-video';
                break;
            case 'flv':
                r = 'fad fa-file-video';
                break;
            case 'mpg':
                r = 'fad fa-file-video';
                break;
            case 'mpeg':
                r = 'fad fa-file-video';
                break;
            case 'ts':
                r = 'fad fa-file-video';
                break;
            case 'mov':
                r = 'fad fa-file-video';
                break;
            case 'vob':
                r = 'fad fa-file-video';
                break;

            case 'png':
                r = 'fad fa-file-image';
                break;
            case 'gif':
                r = 'fad fa-file-image';
                break;
            case 'bmp':
                r = 'fad fa-file-image';
                break;
            case 'jpg':
                r = 'fad fa-file-image';
                break;
            case 'jpeg':
                r = 'fad fa-file-image';
                break;
            case 'webp':
                r = 'fad fa-file-image';
                break;

            case 'ppt':
                r = 'fad fa-file-powerpoint';
                break;
            case 'pptx':
                r = 'fad fa-file-powerpoint';
                break;

            case 'xls':
                r = 'fad fa-file-excel';
                break;
            case 'xlsx':
                r = 'fad fa-file-excel';
                break;
            case 'xlsm':
                r = 'fad fa-file-excel';
                break;

            case 'exe':
                r = 'fad fa-window';
                break;
            case 'bin':
                r = 'fad fa-window';
                break;
            case 'msi':
                r = 'fad fa-window';
                break;
            case 'bat':
                r = 'fad fa-window';
                break;
            case 'sh':
                r = 'fad fa-window';
                break;

            case 'rpm':
                r = 'fad fa-box-alt';
                break;
            case 'deb':
                r = 'fad fa-box-alt';
                break;
            case 'msi':
                r = 'fad fa-box-alt';
                break;
            case 'dmg':
                r = 'fad fa-box-alt';
                break;
            case 'apk':
                r = 'fad fa-box-alt';
                break;

            case 'torrent':
                r = 'fad fa-share-alt-square';
                break;

        }
        return r;
    }

    formatTime(s) {
        var day = Math.floor(s / (24 * 3600));
        var hour = Math.floor((s - day * 24 * 3600) / 3600);
        var minute = Math.floor((s - day * 24 * 3600 - hour * 3600) / 60);
        var second = s - day * 24 * 3600 - hour * 3600 - minute * 60;
        if (hour < 10) {
            hour = '0' + hour.toString();
        }
        if (minute < 10) {
            minute = '0' + minute.toString();
        }
        if (second < 10) {
            second = '0' + second.toString();
        }
        return hour + ":" + minute + ":" + second;
    }

    copyToClip(content) {
        var aux = document.createElement("textarea");
        aux.value = content;
        document.body.appendChild(aux);
        aux.select();
        document.execCommand("copy");
        document.body.removeChild(aux);
    }

    randomString(len) {
        len = len || 32;
        let $chars = 'ABCDEFGHJKMNPQRSTWXYZabcdefhijkmnprstwxyz2345678';
        let maxPos = $chars.length;
        let pwd = '';
        for (let i = 0; i < len; i++) {
            pwd += $chars.charAt(Math.floor(Math.random() * maxPos));
        }
        return pwd;
    }
}